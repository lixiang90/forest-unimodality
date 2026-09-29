import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell471
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (94)
  A := (-9839025174842454762824673 / 5000000000000000000000000)
  B := (433936011768654872344797 / 4000000000000000000000000)
  C := (-16999513591443953224729979 / 10000000000000000000000000000)
  dδ := (58271173045365061426981157 / 1000000000000000000000000000)
  dM := (1104317400536215798556583 / 1000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(301935780064955319734743 / 78125000000000000000000), (44055427879253862499808747 / 500000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9237 / 19012)
  hi := (4631 / 9506)
  vmin := (90291675 / 361456144)
  damping := (90291675 / 361456144)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell471
