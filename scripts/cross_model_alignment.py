"""Train-only PCA + orthogonal alignment of co-located 64D and 128D data.

This tests representation correspondence under matched samples. It does not
establish invertibility, a canonical shared manifold or physical equivalence.
"""
import numpy as np
from sklearn.decomposition import PCA
from sklearn.preprocessing import StandardScaler


def fit_alignment(alpha, tessera, train, test, latent=16, seed=13):
    a=np.asarray(alpha,dtype=float)
    t=np.asarray(tessera,dtype=float)
    train=np.asarray(train,dtype=bool)
    test=np.asarray(test,dtype=bool)
    if (a.ndim != 2 or t.ndim != 2 or a.shape[1] != 64 or t.shape[1] != 128
          or a.shape[0] != t.shape[0] or train.shape != (len(a),)
          or test.shape != (len(a),) or (train & test).any()
          or not np.isfinite(a).all() or not np.isfinite(t).all()
          or not 1 <= latent < min(int(train.sum()),64,128)
          or not test.any()):
        raise ValueError('invalid matched vectors, disjoint folds or latent dimension')
    scaler_a=StandardScaler().fit(a[train])
    scaler_t=StandardScaler().fit(t[train])
    pca_a=PCA(n_components=latent).fit(scaler_a.transform(a[train]))
    pca_t=PCA(n_components=latent).fit(scaler_t.transform(t[train]))
    proj_a=pca_a.transform(scaler_a.transform(a))
    proj_t=pca_t.transform(scaler_t.transform(t))
    cross=proj_t[train].T @ proj_a[train]
    u,_,vt=np.linalg.svd(cross,full_matrices=False)
    rotation=u@vt
    rotated=proj_t@rotation
    denom=float(np.sum(rotated[train]**2))
    if denom <= 0:
        raise ValueError("degenerate latent space")
    scale=float(np.sum(rotated[train]*proj_a[train]) / denom)
    aligned=rotated*scale
    matched=np.linalg.norm(aligned[test]-proj_a[test],axis=1)
    rng=np.random.default_rng(seed)
    shuffled=np.linalg.norm(aligned[test]-proj_a[test][rng.permutation(test.sum())],axis=1)
    return dict(latent_dimension=latent,train_count=int(train.sum()),test_count=int(test.sum()),
                matched_heldout_mean_distance=float(np.mean(matched)),
                shuffled_heldout_mean_distance=float(np.mean(shuffled)),
                label='PCA and orthogonal Procrustes fit on train rows ONLY',
                limitation='co-location and statistical alignment do not prove physical equivalence')
