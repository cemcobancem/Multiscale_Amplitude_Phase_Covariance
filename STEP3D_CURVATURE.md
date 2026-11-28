# Step 3D — curvature and geometric conservation

Starting baseline: main c590b4cbbf417506fe60e5eaf23d8268fea5e120, successful main run 46124949894, 323 certified declarations. All nine prior Lean modules and all five ledgers remain frozen.

## First checkpoint
Step3D.lean introduces actual coordinate derivatives of connection coefficients, Riemann curvature with convention R(X,Y)Z = ∇X∇YZ − ∇Y∇XZ − ∇[X,Y]Z, Ricci and scalar contractions, Einstein tensor expression, skew symmetry in curvature directions and flat Minkowski regression. 7 theorem candidates and 5 definitions; 335 total targets. Await both CI runs. Coordinate formulas are not yet intrinsic tensors.

## Remaining gates
1. Derive curvature from the actual Step 3C covariant derivative and prove multilinearity, germ locality and chart independence; impose and track sufficient differentiability.
2. First Bianchi identity from torsion freedom; metric-lowered curvature symmetries and Ricci symmetry.
3. Intrinsic covariant derivative of curvature and second Bianchi identity; derive contracted Bianchi and divergence-free Einstein tensor, with no conservation assumption.
4. Verify nonflat benchmark and flat limit; review actual tensor contraction and signs.
5. Audit all declarations against all five frozen ledgers; independent mathematical scope review and owner-approved consolidation.

Einstein field equations, a physical quantum-to-Lorentzian map, stress-energy sourcing, and empirical claims are not consequences of the geometric identities alone. No Step 3E or main merge without approval.

## Verified first checkpoint and second candidate checkpoint

Commit 4ccade19a86905cfb1442ce9d077e2f759a7dbca passed push 46126385940 and PR 46126390062; 335/335 clean in both, 670 reports each, exact agreement and all five earlier ledgers matched. Frozen evidence: STEP3D_335_AXIOM_AUDIT.tsv. Step3D.lean frozen at blob 4ebb428a44a86474559a781ed1ff7a0086f0ecea. Step3DBianchi.lean adds 5 theorem candidates and one definition (341 total): derivative symmetry from torsion-free coefficient fields, coordinate first Bianchi identity, metric-Christoffel specialization, intrinsic commutator and intrinsic skew symmetry under the stated metric regularity. Intrinsic tensoriality, agreement with coordinate curvature, and the second Bianchi identity remain outstanding. No merge.

## Certified 341 checkpoint and actual curvature tensor candidates

Commit 9d1a48c359a29bde298fbd29b6f1fd352f938ab6 passed push 46127436451 and PR 46127441230. All 341 declarations clean and exact cross-run agreement; all six prior ledgers matched. New frozen ledger STEP3D_341_AXIOM_AUDIT.tsv; Step3DBianchi.lean frozen at 0dac2ab381a1d6c4dc6adb4027922639301cec5f. Step3DTensor.lean adds 16 theorem candidates and 1 definition(s) (358 total). Actual local covariant commutator expansion, pointwise trilinearity, component basis comparison, field/covariant germ locality and smooth chart output, and canonical intrinsic commutator comparison are attempted. All new results await compilation. Intrinsic all-slot laws and arbitrary-chart curvature transformation, intrinsic first Bianchi and metric-lowered symmetries, curvature smooth closure, Ricci symmetry and differential Bianchi remain further obligations. No merge or later step.
