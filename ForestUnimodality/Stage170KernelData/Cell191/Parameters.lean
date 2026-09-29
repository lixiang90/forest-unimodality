import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell191
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (257)
  A := (-2153897627816106415110653 / 1250000000000000000000000)
  B := (24512788729423792832839979 / 500000000000000000000000000)
  C := (4790725478543294852534773 / 2500000000000000000000000000)
  dδ := (29890539136456076296788353 / 1000000000000000000000000000)
  dM := (24866645554324113024866061 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(23749229990963776515400241 / 500000000000000000000000), (20775045766687452442056383 / 100000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11 / 21)
  hi := (111 / 211)
  vmin := (11100 / 44521)
  damping := (11100 / 44521)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell191
