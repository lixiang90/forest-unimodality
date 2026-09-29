import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell534
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (67)
  A := (-34857833006462876134889939 / 50000000000000000000000000)
  B := (15241728230888366979467463 / 250000000000000000000000000)
  C := (1736757909706918290293487 / 10000000000000000000000000)
  dδ := (2483474890522034857209821 / 62500000000000000000000000)
  dM := (28940804899205694374758613 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(72274254014869754314531747 / 10000000000000000000000000), (21316122829357954771012373 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (116 / 207)
  hi := (13 / 23)
  vmin := (130 / 529)
  damping := (130 / 529)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell534
