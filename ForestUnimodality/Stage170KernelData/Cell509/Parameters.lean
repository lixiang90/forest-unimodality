import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell509
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (101)
  A := (-10378919045130878490112991 / 5000000000000000000000000)
  B := (10892934835859113817946309 / 100000000000000000000000000)
  C := (6812092730233902486414177 / 2000000000000000000000000000)
  dδ := (5678199438262968717916479 / 100000000000000000000000000)
  dM := (2666900338908038828669711 / 2500000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(39863382241130431715703253 / 5000000000000000000000000), (45449086897365106096913223 / 500000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1531 / 2926)
  hi := (11 / 21)
  vmin := (110 / 441)
  damping := (110 / 441)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell509
