import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 38
  A := (-78206001627799231034288141/100000000000000000000000000)
  B := (5874758186682227378838661/50000000000000000000000000)
  C := (-22029944410236151908222269/100000000000000000000000000)
  dδ := (71543941894187598751209123/1000000000000000000000000000)
  dM := (9946749135447375492896649/5000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(35643611494934397398992587/5000000000000000000000000), (76928091353376188976653793/10000000000000000000000000)]
  retention := ![(3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7/17)
  hi := (64/153)
  vmin := (70/289)
  damping := (70/289)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell021
