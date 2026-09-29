import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell310
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (37)
  A := (-21642649573657902752898963 / 1000000000000000000000000000)
  B := (20005182642960701866474693 / 1000000000000000000000000000)
  C := (10654656599002280265020559 / 250000000000000000000000000)
  dδ := (15236253441441680034351691 / 1000000000000000000000000000)
  dM := (1294059741314890405773641 / 10000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(555311064861291541205901 / 40000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (33 / 53)
  hi := (467 / 742)
  vmin := (128425 / 550564)
  damping := (128425 / 550564)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell310
