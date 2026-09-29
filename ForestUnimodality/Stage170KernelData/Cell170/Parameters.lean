import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell170
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (212)
  A := (-15990608946473462881243677 / 10000000000000000000000000)
  B := (10666697121646656620796989 / 200000000000000000000000000)
  C := (6618473147088335586246677 / 5000000000000000000000000000)
  dδ := (34084680420784371768228027 / 1000000000000000000000000000)
  dM := (3098339700399652639484227 / 10000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(12009172170613956254214827 / 500000000000000000000000), (18634984377833336566254729 / 100000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53 / 103)
  hi := (107 / 207)
  vmin := (10700 / 42849)
  damping := (10700 / 42849)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell170
