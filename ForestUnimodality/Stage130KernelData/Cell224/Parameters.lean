import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell224
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 50
  A := (-1823409286951154855103141/4000000000000000000000000)
  B := (30143899352582395612110133/500000000000000000000000000)
  C := (7821822646328115136160619/50000000000000000000000000)
  dδ := (164578749597121918191861/3906250000000000000000000)
  dM := (67417665894139923877387277/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(4712649375620820535459643/1000000000000000000000000), (30840969020456472371449763/5000000000000000000000000), (3896536652163300118445477/400000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (27/47)
  hi := (653/1128)
  vmin := (310175/1272384)
  damping := (310175/1272384)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell224
