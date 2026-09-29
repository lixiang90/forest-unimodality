import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 61
  A := (-50656791034220132296184147/100000000000000000000000000)
  B := (72979557143617354575404477/1000000000000000000000000000)
  C := (15768756276350942222008733/5000000000000000000000000000)
  dδ := (78633935202252466800665331/1000000000000000000000000000)
  dM := (5315059018747343320618337/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(7329134312742565660059313/5000000000000000000000000), (2958506040080598964436831/400000000000000000000000), (5289218539894132931067361/500000000000000000000000), (10244358215796026456700929/250000000000000000000000)]
  retention := ![(4/5), (7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22597/43472)
  hi := (11311/21736)
  vmin := (117917175/472453696)
  damping := (117917175/472453696)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell103
