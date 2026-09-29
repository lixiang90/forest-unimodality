import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell409
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (56)
  A := (-3692545127153768903749409 / 6250000000000000000000000)
  B := (124442479532843961603783 / 2500000000000000000000000)
  C := (11475990788233303430132537 / 100000000000000000000000000)
  dδ := (14242204049425822437457967 / 500000000000000000000000000)
  dM := (21616545002743926535797303 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(37926908425040711803077897 / 100000000000000000000000000), (2271647661346634805568101 / 100000000000000000000000)]
  retention := ![(7 / 10), (3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (27 / 47)
  hi := (653 / 1128)
  vmin := (310175 / 1272384)
  damping := (310175 / 1272384)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell409
