import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell412
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (47)
  A := (-1371659463590780508823741 / 5000000000000000000000000)
  B := (37430933130262689090272943 / 1000000000000000000000000000)
  C := (9126020958489582113326577 / 100000000000000000000000000)
  dδ := (1604874532197673141220573 / 62500000000000000000000000)
  dM := (31766190544689964711522201 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(629037055787422416663901 / 125000000000000000000000), (6949332840552312262616397 / 500000000000000000000000)]
  retention := ![(7 / 10), (3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53 / 90)
  hi := (107 / 180)
  vmin := (7811 / 32400)
  damping := (7811 / 32400)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell412
