import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell378
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (131)
  A := (-135464905760986348715047 / 78125000000000000000000)
  B := (96825428452569126114291009 / 1000000000000000000000000000)
  C := (-2161056456889185253822383 / 6250000000000000000000000)
  dδ := (12060095335727663568015089 / 200000000000000000000000000)
  dM := (10675227583454922257542169 / 12500000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(5798331153610996047120807 / 500000000000000000000000), (47582476325426213747959991 / 1000000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1613 / 3478)
  hi := (22 / 47)
  vmin := (3008245 / 12096484)
  damping := (3008245 / 12096484)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell378
