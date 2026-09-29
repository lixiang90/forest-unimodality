import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 56
  A := (46023534026498231664703553/100000000000000000000000000)
  B := (37912891555705013901800271/1000000000000000000000000000)
  C := (-48011331649600404907277107/100000000000000000000000000000)
  dδ := (84079811022481992788257799/1000000000000000000000000000)
  dM := (19335218220039869074095007/25000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(1299279647322199249259711/250000000000000000000000), (28242710815864993101342861/10000000000000000000000000), (1934210238867347868563229/40000000000000000000000)]
  retention := ![(4/5), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3193/6468)
  hi := (49/99)
  vmin := (10457075/41835024)
  damping := (10457075/41835024)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell055
