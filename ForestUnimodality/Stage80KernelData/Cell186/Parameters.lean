import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell186
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 78
  A := (-6403301646114761497230461/5000000000000000000000000)
  B := (250096941544910890409259/1250000000000000000000000)
  C := (12683670492944163488147069/20000000000000000000000000)
  dδ := (2089391137989014129994203/12500000000000000000000000)
  dM := (3936758171689236016077551/1000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(17866814863722275674717821/2000000000000000000000000), (4986315424039856480931121/200000000000000000000000)]
  retention := ![(3/5), (1/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (427/792)
  hi := (2567/4752)
  vmin := (5608895/22581504)
  damping := (5608895/22581504)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell186
