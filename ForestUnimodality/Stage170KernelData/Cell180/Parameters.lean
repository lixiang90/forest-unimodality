import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell180
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (210)
  A := (-16787186505626038768212993 / 10000000000000000000000000)
  B := (27669109053192524061426383 / 500000000000000000000000000)
  C := (3505875693131019037174223 / 2000000000000000000000000000)
  dδ := (34184685885530911864105263 / 1000000000000000000000000000)
  dM := (32257764289319148034995699 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(11228889751774074667878267 / 500000000000000000000000), (18583108009785027547877689 / 100000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (27 / 52)
  hi := (109 / 209)
  vmin := (10900 / 43681)
  damping := (10900 / 43681)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell180
