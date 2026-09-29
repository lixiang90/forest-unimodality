import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell432
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (23)
  A := (535252052805663054471097 / 4000000000000000000000000)
  B := (1519939136155525061244731 / 100000000000000000000000000)
  C := (-11479762322291061152346181 / 500000000000000000000000000)
  dδ := (7726468223598834984822137 / 500000000000000000000000000)
  dM := (8623064788646236749052737 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(31644347456314041444613849 / 10000000000000000000000000), (35024043778940363580431949 / 10000000000000000000000000)]
  retention := ![(1 / 2), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (39 / 140)
  hi := (2 / 7)
  vmin := (3939 / 19600)
  damping := (393900000000000000000000000000000000000000 / 4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell432
