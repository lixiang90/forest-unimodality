import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell536
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (61)
  A := (-18284581730062208798415213 / 25000000000000000000000000)
  B := (12466216077548381013784251 / 200000000000000000000000000)
  C := (15052226601443091658083517 / 100000000000000000000000000)
  dδ := (36251258983683191938762747 / 1000000000000000000000000000)
  dM := (11900361896039061450347507 / 20000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(10695018734500376211826733 / 500000000000000000000000), (20350970575885138913463379 / 5000000000000000000000000)]
  retention := ![(3 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (21 / 37)
  hi := (53 / 93)
  vmin := (2120 / 8649)
  damping := (2120 / 8649)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell536
