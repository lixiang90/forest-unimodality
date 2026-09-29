import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell219
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 62
  A := (-4128036488710123554035647/6250000000000000000000000)
  B := (17706717365467673774848123/250000000000000000000000000)
  C := (20363449615292900096719109/100000000000000000000000000)
  dδ := (49086579991985679338739601/1000000000000000000000000000)
  dM := (39543363220551650070305749/50000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(32045325867076970283164883/5000000000000000000000000), (311465258743579997968709/15625000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (116/207)
  hi := (13/23)
  vmin := (130/529)
  damping := (130/529)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell219
