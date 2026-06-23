#!/usr/bin/env python3
"""Vulkan incidence matvec for NS triad-pair Laplacians.

This backend is a matvec engine only.  It consumes the edge incidence arrays
from ``ns_triad_kn_matrix_free_operator`` and returns ``L_abs x`` or
``L_neg x`` in float32.  Eigensolver control and promotion decisions remain on
the CPU side.
"""

from __future__ import annotations

import math
import os
import platform
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

import numpy as np

SCRIPT_DIR = Path(__file__).resolve().parent
DASHI_CORE_ROOT = Path("/home/c/Documents/code/dashiCORE")
if DASHI_CORE_ROOT.exists() and str(DASHI_CORE_ROOT) not in sys.path:
    sys.path.insert(0, str(DASHI_CORE_ROOT))

try:
    import vulkan as vk
    from gpu_vulkan_dispatcher import (  # type: ignore
        HOST_VISIBLE_COHERENT,
        VulkanDispatchConfig,
        VulkanHandles,
        _create_buffer,
        _read_buffer,
        _require_vk,
        _write_buffer,
        create_vulkan_handles,
    )
except Exception:  # pragma: no cover - depends on local Vulkan environment
    vk = None  # type: ignore
    HOST_VISIBLE_COHERENT = 0  # type: ignore
    VulkanDispatchConfig = Any  # type: ignore
    VulkanHandles = Any  # type: ignore
    _create_buffer = None  # type: ignore
    _read_buffer = None  # type: ignore
    _require_vk = None  # type: ignore
    _write_buffer = None  # type: ignore
    create_vulkan_handles = None  # type: ignore

from ns_triad_kn_matrix_free_operator import MatrixFreeKNProfile  # type: ignore  # noqa: E402


SHADER_PATH = SCRIPT_DIR / "triad_laplacian_matvec.comp"
DEFAULT_SPV_PATH = Path("/tmp/dashi_agda_spv/triad_laplacian_matvec.spv")
DEFAULT_VULKAN_ICD_CANDIDATES = (
    Path("/usr/share/vulkan/icd.d/radeon_icd.x86_64.json"),
    Path("/usr/share/vulkan/icd.d/radeon_icd.json"),
    Path("/usr/share/vulkan/icd.d/amd_icd64.json"),
    Path("/usr/share/vulkan/icd.d/nvidia_icd.json"),
)


def _icd_candidates() -> list[Path]:
    """Return dashiCORE-style ICD candidates, preferring documented RADV names."""

    seen: set[Path] = set()
    candidates: list[Path] = []
    for candidate in DEFAULT_VULKAN_ICD_CANDIDATES:
        if candidate not in seen:
            candidates.append(candidate)
            seen.add(candidate)
    for parent in (Path("/usr/share/vulkan/icd.d"), Path("/etc/vulkan/icd.d")):
        if parent.is_dir():
            for candidate in sorted(parent.glob("*.json")):
                if candidate not in seen:
                    candidates.append(candidate)
                    seen.add(candidate)
    return candidates


def _set_icd(icd_path: str | Path | None) -> str | None:
    if icd_path is None:
        return None
    path = str(icd_path)
    os.environ["VK_ICD_FILENAMES"] = path
    return path


def has_vulkan_triad_laplacian() -> bool:
    """Return True when Python Vulkan bindings and glslc are available."""

    if vk is None or _require_vk is None:
        return False
    try:
        _require_vk()
        subprocess.run(["glslc", "--version"], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        return True
    except Exception:
        return False


def compile_shader(spv_path: Path = DEFAULT_SPV_PATH) -> Path:
    """Compile the local GLSL shader into /tmp so sibling repos stay untouched."""

    if not SHADER_PATH.exists():
        raise FileNotFoundError(SHADER_PATH)
    spv_path.parent.mkdir(parents=True, exist_ok=True)
    if spv_path.exists() and spv_path.stat().st_mtime >= SHADER_PATH.stat().st_mtime:
        return spv_path
    subprocess.run(["glslc", str(SHADER_PATH), "-o", str(spv_path)], check=True)
    return spv_path


class VulkanTriadLaplacianExecutor:
    """Reusable Vulkan executor for a fixed triad incidence profile."""

    def __init__(
        self,
        profile: MatrixFreeKNProfile,
        *,
        handles: VulkanHandles | None = None,
        dispatch_config: VulkanDispatchConfig | None = None,
        spv_path: Path = DEFAULT_SPV_PATH,
        workgroup_size: int = 256,
        icd_path: str | Path | None = None,
    ) -> None:
        if vk is None or _require_vk is None:
            raise RuntimeError("vulkan python package not installed")
        self.icd_path = _set_icd(icd_path if icd_path is not None else os.environ.get("VK_ICD_FILENAMES"))
        _require_vk()
        self.profile = profile
        self.mode_count = int(profile.mode_count)
        self.edge_count = int(len(profile.edge_left))
        self.workgroup_size = int(workgroup_size)
        self.spv_path = compile_shader(spv_path)
        self.external_handles = handles
        self.handles = handles or create_vulkan_handles(dispatch_config or VulkanDispatchConfig())
        self._owns_handles = handles is None
        self.device = self.handles.device
        self.queue = self.handles.queue
        self.mem_props = self.handles.mem_props
        self.queue_family_index = self.handles.queue_family_index
        self._build_pipeline()
        self._allocate_buffers()

    def _build_pipeline(self) -> None:
        bindings = [
            vk.VkDescriptorSetLayoutBinding(
                binding=index,
                descriptorType=vk.VK_DESCRIPTOR_TYPE_STORAGE_BUFFER,
                descriptorCount=1,
                stageFlags=vk.VK_SHADER_STAGE_COMPUTE_BIT,
                pImmutableSamplers=None,
            )
            for index in range(5)
        ]
        layout_info = vk.VkDescriptorSetLayoutCreateInfo(
            sType=vk.VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO,
            bindingCount=len(bindings),
            pBindings=bindings,
        )
        self.descriptor_set_layout = vk.vkCreateDescriptorSetLayout(self.device, layout_info, None)
        push_constant_range = vk.VkPushConstantRange(
            stageFlags=vk.VK_SHADER_STAGE_COMPUTE_BIT,
            offset=0,
            size=8,
        )
        pipeline_layout_info = vk.VkPipelineLayoutCreateInfo(
            sType=vk.VK_STRUCTURE_TYPE_PIPELINE_LAYOUT_CREATE_INFO,
            setLayoutCount=1,
            pSetLayouts=[self.descriptor_set_layout],
            pushConstantRangeCount=1,
            pPushConstantRanges=[push_constant_range],
        )
        self.pipeline_layout = vk.vkCreatePipelineLayout(self.device, pipeline_layout_info, None)
        shader_code = self.spv_path.read_bytes()
        module_info = vk.VkShaderModuleCreateInfo(
            sType=vk.VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO,
            codeSize=len(shader_code),
            pCode=shader_code,
        )
        self.shader_module = vk.vkCreateShaderModule(self.device, module_info, None)
        stage_info = vk.VkPipelineShaderStageCreateInfo(
            sType=vk.VK_STRUCTURE_TYPE_PIPELINE_SHADER_STAGE_CREATE_INFO,
            stage=vk.VK_SHADER_STAGE_COMPUTE_BIT,
            module=self.shader_module,
            pName="main",
        )
        pipeline_info = vk.VkComputePipelineCreateInfo(
            sType=vk.VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO,
            stage=stage_info,
            layout=self.pipeline_layout,
        )
        self.pipeline = vk.vkCreateComputePipelines(self.device, vk.VK_NULL_HANDLE, 1, [pipeline_info], None)[0]
        pool_sizes = [vk.VkDescriptorPoolSize(type=vk.VK_DESCRIPTOR_TYPE_STORAGE_BUFFER, descriptorCount=5)]
        pool_info = vk.VkDescriptorPoolCreateInfo(
            sType=vk.VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO,
            maxSets=1,
            poolSizeCount=len(pool_sizes),
            pPoolSizes=pool_sizes,
        )
        self.descriptor_pool = vk.vkCreateDescriptorPool(self.device, pool_info, None)
        alloc_info = vk.VkDescriptorSetAllocateInfo(
            sType=vk.VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO,
            descriptorPool=self.descriptor_pool,
            descriptorSetCount=1,
            pSetLayouts=[self.descriptor_set_layout],
        )
        self.descriptor_set = vk.vkAllocateDescriptorSets(self.device, alloc_info)[0]

    def _allocate_buffers(self) -> None:
        usage = vk.VK_BUFFER_USAGE_STORAGE_BUFFER_BIT
        flags = HOST_VISIBLE_COHERENT
        edge_bytes = max(1, self.edge_count) * np.dtype(np.uint32).itemsize
        weight_bytes = max(1, self.edge_count) * np.dtype(np.float32).itemsize
        vec_bytes = max(1, self.mode_count) * np.dtype(np.float32).itemsize
        self.buf_left, self.mem_left = _create_buffer(self.device, self.mem_props, edge_bytes, usage, flags)
        self.buf_right, self.mem_right = _create_buffer(self.device, self.mem_props, edge_bytes, usage, flags)
        self.buf_weight, self.mem_weight = _create_buffer(self.device, self.mem_props, weight_bytes, usage, flags)
        self.buf_x, self.mem_x = _create_buffer(self.device, self.mem_props, vec_bytes, usage, flags)
        self.buf_y, self.mem_y = _create_buffer(self.device, self.mem_props, vec_bytes, usage, flags)

        left = np.asarray(self.profile.edge_left, dtype=np.uint32, order="C")
        right = np.asarray(self.profile.edge_right, dtype=np.uint32, order="C")
        if self.edge_count == 0:
            left = np.zeros(1, dtype=np.uint32)
            right = np.zeros(1, dtype=np.uint32)
        _write_buffer(self.device, self.mem_left, left)
        _write_buffer(self.device, self.mem_right, right)
        self._update_descriptors(edge_bytes, weight_bytes, vec_bytes)

        pool_info = vk.VkCommandPoolCreateInfo(
            sType=vk.VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO,
            queueFamilyIndex=self.queue_family_index,
            flags=vk.VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT,
        )
        self.command_pool = vk.vkCreateCommandPool(self.device, pool_info, None)
        alloc_info = vk.VkCommandBufferAllocateInfo(
            sType=vk.VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO,
            commandPool=self.command_pool,
            level=vk.VK_COMMAND_BUFFER_LEVEL_PRIMARY,
            commandBufferCount=1,
        )
        self.command_buffer = vk.vkAllocateCommandBuffers(self.device, alloc_info)[0]

    def _update_descriptors(self, edge_bytes: int, weight_bytes: int, vec_bytes: int) -> None:
        buffers = [
            (self.buf_left, edge_bytes),
            (self.buf_right, edge_bytes),
            (self.buf_weight, weight_bytes),
            (self.buf_x, vec_bytes),
            (self.buf_y, vec_bytes),
        ]
        write_sets = [
            vk.VkWriteDescriptorSet(
                sType=vk.VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET,
                dstSet=self.descriptor_set,
                dstBinding=index,
                descriptorCount=1,
                descriptorType=vk.VK_DESCRIPTOR_TYPE_STORAGE_BUFFER,
                pBufferInfo=[vk.VkDescriptorBufferInfo(buffer=buffer, offset=0, range=size)],
            )
            for index, (buffer, size) in enumerate(buffers)
        ]
        vk.vkUpdateDescriptorSets(self.device, len(write_sets), write_sets, 0, None)

    def matvec(self, x: np.ndarray, weights: np.ndarray) -> np.ndarray:
        vec = np.asarray(x, dtype=np.float32, order="C")
        if vec.ndim != 1 or int(vec.shape[0]) != self.mode_count:
            raise ValueError(f"x must be length {self.mode_count}")
        weights32 = np.asarray(weights, dtype=np.float32, order="C")
        if int(weights32.shape[0]) != self.edge_count:
            raise ValueError(f"weights must be length {self.edge_count}")
        if self.edge_count == 0:
            weights32 = np.zeros(1, dtype=np.float32)
        _write_buffer(self.device, self.mem_weight, weights32)
        _write_buffer(self.device, self.mem_x, vec)

        begin_info = vk.VkCommandBufferBeginInfo(
            sType=vk.VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO,
            flags=vk.VK_COMMAND_BUFFER_USAGE_ONE_TIME_SUBMIT_BIT,
        )
        vk.vkBeginCommandBuffer(self.command_buffer, begin_info)
        vk.vkCmdBindPipeline(self.command_buffer, vk.VK_PIPELINE_BIND_POINT_COMPUTE, self.pipeline)
        vk.vkCmdBindDescriptorSets(
            self.command_buffer,
            vk.VK_PIPELINE_BIND_POINT_COMPUTE,
            self.pipeline_layout,
            0,
            1,
            [self.descriptor_set],
            0,
            None,
        )
        if hasattr(vk, "ffi"):
            push_data = vk.ffi.new("uint32_t[]", [self.mode_count, self.edge_count])
        else:
            push_data = np.asarray([self.mode_count, self.edge_count], dtype=np.uint32)
        vk.vkCmdPushConstants(
            self.command_buffer,
            self.pipeline_layout,
            vk.VK_SHADER_STAGE_COMPUTE_BIT,
            0,
            8,
            push_data,
        )
        groups = math.ceil(self.mode_count / self.workgroup_size)
        vk.vkCmdDispatch(self.command_buffer, groups, 1, 1)
        vk.vkEndCommandBuffer(self.command_buffer)
        submit_info = vk.VkSubmitInfo(
            sType=vk.VK_STRUCTURE_TYPE_SUBMIT_INFO,
            commandBufferCount=1,
            pCommandBuffers=[self.command_buffer],
        )
        fence = vk.vkCreateFence(
            self.device,
            vk.VkFenceCreateInfo(sType=vk.VK_STRUCTURE_TYPE_FENCE_CREATE_INFO),
            None,
        )
        vk.vkQueueSubmit(self.queue, 1, [submit_info], fence)
        started = time.perf_counter()
        result = vk.vkWaitForFences(self.device, 1, [fence], vk.VK_TRUE, 10_000_000_000)
        elapsed_ms = 1000.0 * (time.perf_counter() - started)
        vk.vkDestroyFence(self.device, fence, None)
        if result not in (None, vk.VK_SUCCESS):
            raise RuntimeError(f"vkWaitForFences failed with code {result}")
        out = _read_buffer(self.device, self.mem_y, (self.mode_count,), np.float32)
        vk.vkResetCommandBuffer(self.command_buffer, 0)
        self.last_fence_wait_ms = elapsed_ms
        return np.asarray(out, dtype=np.float64)

    def matvec_abs(self, x: np.ndarray) -> np.ndarray:
        return self.matvec(x, self.profile.weights_abs)

    def matvec_neg(self, x: np.ndarray) -> np.ndarray:
        return self.matvec(x, self.profile.weights_neg)

    def close(self) -> None:
        if vk is None or not getattr(self, "device", None):
            return
        for name in ("left", "right", "weight", "x", "y"):
            buffer = getattr(self, f"buf_{name}", None)
            memory = getattr(self, f"mem_{name}", None)
            if buffer is not None:
                vk.vkDestroyBuffer(self.device, buffer, None)
            if memory is not None:
                vk.vkFreeMemory(self.device, memory, None)
        if hasattr(self, "command_pool"):
            vk.vkDestroyCommandPool(self.device, self.command_pool, None)
        if hasattr(self, "pipeline"):
            vk.vkDestroyPipeline(self.device, self.pipeline, None)
        if hasattr(self, "pipeline_layout"):
            vk.vkDestroyPipelineLayout(self.device, self.pipeline_layout, None)
        if hasattr(self, "shader_module"):
            vk.vkDestroyShaderModule(self.device, self.shader_module, None)
        if hasattr(self, "descriptor_pool"):
            vk.vkDestroyDescriptorPool(self.device, self.descriptor_pool, None)
        if hasattr(self, "descriptor_set_layout"):
            vk.vkDestroyDescriptorSetLayout(self.device, self.descriptor_set_layout, None)
        if self._owns_handles and self.handles is not None:
            self.handles.close()


def _probe_once(profile: MatrixFreeKNProfile, icd_path: Path | None) -> tuple[VulkanTriadLaplacianExecutor | None, str | None, str | None]:
    try:
        executor = VulkanTriadLaplacianExecutor(profile, icd_path=icd_path)
        return executor, executor.icd_path, None
    except Exception as exc:  # noqa: BLE001
        return None, str(icd_path) if icd_path is not None else None, f"{type(exc).__name__}: {exc}"


def create_vulkan_triad_laplacian_executor(
    profile: MatrixFreeKNProfile,
) -> tuple[VulkanTriadLaplacianExecutor, dict[str, Any]]:
    """Create an executor using the dashiCORE ICD probe convention."""

    if os.environ.get("VK_ICD_FILENAMES"):
        executor, icd, error = _probe_once(profile, Path(os.environ["VK_ICD_FILENAMES"]))
        if executor is not None:
            return executor, {"vulkan_icd": icd, "icd_probe_errors": []}
        raise RuntimeError(f"explicit Vulkan ICD failed ({icd}): {error}")

    errors: list[dict[str, str | None]] = []
    for candidate in _icd_candidates():
        if not candidate.is_file():
            continue
        executor, icd, error = _probe_once(profile, candidate)
        if executor is not None:
            return executor, {"vulkan_icd": icd, "icd_probe_errors": errors}
        errors.append({"icd": str(candidate), "error": error})
    uname = platform.uname()
    raise RuntimeError(
        "no Vulkan ICD initialized; "
        f"system={uname.system} {uname.release} {uname.machine}; "
        f"probe_errors={errors}"
    )
