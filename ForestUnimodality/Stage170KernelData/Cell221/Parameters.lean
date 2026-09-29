import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell221
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (100)
  A := (-95107718251812893960561723 / 100000000000000000000000000)
  B := (57745742449513845495623343 / 1000000000000000000000000000)
  C := (3907655313617030556905263 / 20000000000000000000000000)
  dδ := (36108183729728009214721141 / 1000000000000000000000000000)
  dM := (44385836204874622602095657 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(49879456065981591095237491 / 10000000000000000000000000), (39284041716018592182990687 / 1000000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (6 / 11)
  hi := (97 / 177)
  vmin := (7760 / 31329)
  damping := (7760 / 31329)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell221
