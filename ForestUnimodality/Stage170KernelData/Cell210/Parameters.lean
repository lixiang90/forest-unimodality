import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell210
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (156)
  A := (-134402665685399240857123 / 100000000000000000000000)
  B := (52866856033078009347025983 / 1000000000000000000000000000)
  C := (1087663315979281591916461 / 5000000000000000000000000)
  dδ := (32156462825386603054944601 / 1000000000000000000000000000)
  dM := (30830978281782737103478009 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(96054268620654559285299 / 6250000000000000000000), (3495925468718892759056871 / 62500000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (57 / 107)
  hi := (29 / 54)
  vmin := (725 / 2916)
  damping := (725 / 2916)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell210
