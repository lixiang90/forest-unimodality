import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 22
  A := (5642759493417945860116447/50000000000000000000000000)
  B := (3802260118435952032656111/250000000000000000000000000)
  C := (-24261736722591391995917931/1000000000000000000000000000)
  dδ := (934764924768152717302061/62500000000000000000000000)
  dM := (1471792171670784144438043/15625000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(42044592898265037428373603/50000000000000000000000000), (2347070396521927193589363/400000000000000000000000)]
  retention := ![(3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (37/126)
  hi := (19/63)
  vmin := (3293/15876)
  damping := (32930000000000000000000000000000000000000000/391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell006
