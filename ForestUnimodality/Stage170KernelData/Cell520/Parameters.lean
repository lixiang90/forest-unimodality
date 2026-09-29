import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell520
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (100)
  A := (-10251197247453786803816911 / 5000000000000000000000000)
  B := (2729390660255441580783753 / 25000000000000000000000000)
  C := (42988774406110888404164427 / 10000000000000000000000000000)
  dδ := (29354334648200652163607671 / 500000000000000000000000000)
  dM := (10768959578305499231315467 / 10000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(66477188068888120042743139 / 10000000000000000000000000), (91247641951765430690102221 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11953 / 22578)
  hi := (7977 / 15052)
  vmin := (56437275 / 226562704)
  damping := (56437275 / 226562704)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell520
