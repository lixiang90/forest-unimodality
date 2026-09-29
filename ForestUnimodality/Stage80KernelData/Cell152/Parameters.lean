import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (8293349900307292966061823/50000000000000000000000000)
  B := (34282331947913538550132273/500000000000000000000000000)
  C := (70788269435760522302336639/10000000000000000000000000000)
  dδ := (5971311531311621068063289/50000000000000000000000000)
  dM := (16484747465128049472710137/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(72557967681230843837170141/10000000000000000000000000), (12748789442378843261849397/500000000000000000000000), (15750384853606793633673533/2500000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (47737/90312)
  hi := (31833/60208)
  vmin := (903261375/3625003264)
  damping := (903261375/3625003264)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell152
