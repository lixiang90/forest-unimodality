import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell497
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (102)
  A := (-8890035603829679838838729 / 5000000000000000000000000)
  B := (95684510656733806621687677 / 1000000000000000000000000000)
  C := (3086706091123202449870433 / 1250000000000000000000000000)
  dδ := (56560544242561412719982883 / 1000000000000000000000000000)
  dM := (5755276513082960537347893 / 6250000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(1074679019205065921838127 / 125000000000000000000000), (9157047954617554808010027 / 100000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7339 / 14214)
  hi := (107 / 207)
  vmin := (10700 / 42849)
  damping := (10700 / 42849)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell497
