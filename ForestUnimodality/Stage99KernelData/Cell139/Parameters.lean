import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 120
  A := (207101423758012568328013/2000000000000000000000000)
  B := (588306247157286202331683/6250000000000000000000000)
  C := (68086058628101142620181463/100000000000000000000000000)
  dδ := (14757563953431934722360097/100000000000000000000000000)
  dM := (405694611089446848916501/250000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(66252811414956145341648153/10000000000000000000000000), (41358540468101345766172017/10000000000000000000000000), (24041472272627970596658997/1000000000000000000000000), (4195327215815260757381111/200000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (15929/30104)
  hi := (95599/180624)
  vmin := (8128304975/32625029376)
  damping := (8128304975/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell139
