import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell531
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (81)
  A := (-12505280694328839052786861 / 10000000000000000000000000)
  B := (20758722508545140311708721 / 250000000000000000000000000)
  C := (21119515178640022035061463 / 100000000000000000000000000)
  dδ := (5496819970065239951972913 / 125000000000000000000000000)
  dM := (79063068566591928991449389 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(38867698577871720999610261 / 10000000000000000000000000), (593041315975349148104101 / 125000000000000000000000), (5253541243090541001947713 / 200000000000000000000000)]
  retention := ![(7 / 10), (3 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (49 / 89)
  hi := (99 / 179)
  vmin := (7920 / 32041)
  damping := (7920 / 32041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell531
