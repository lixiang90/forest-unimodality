import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (-15668843027879357897802493/100000000000000000000000000)
  B := (91783211251732749191845073/1000000000000000000000000000)
  C := (17691748006060223265961673/5000000000000000000000000000)
  dδ := (2985123359387564789813041/25000000000000000000000000)
  dM := (10328102448776926673701393/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(226876546701835248021073/39062500000000000000000), (68235363246643332413299277/100000000000000000000000000), (6447412351382699569057877/200000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3579/7004)
  hi := (5381/10506)
  vmin := (27577625/110376036)
  damping := (27577625/110376036)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell096
