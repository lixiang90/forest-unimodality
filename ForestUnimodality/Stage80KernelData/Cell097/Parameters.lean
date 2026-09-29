import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (-27282492981250266005588401/100000000000000000000000000)
  B := (49793415107160100829819527/500000000000000000000000000)
  C := (37607775002884607021269581/10000000000000000000000000000)
  dδ := (11865088876080691349113039/100000000000000000000000000)
  dM := (11012810620662052182167079/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(27871001755295181645522007/5000000000000000000000000), (29408210812476220930022919/5000000000000000000000000), (67891131113431839594341/2500000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (5381/10506)
  hi := (10787/21012)
  vmin := (110297075/441504144)
  damping := (110297075/441504144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell097
