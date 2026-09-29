import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 39
  A := (-11768342336271725889673689/10000000000000000000000000)
  B := (3144530145460517900346531/20000000000000000000000000)
  C := (-72483503341252116317083853/10000000000000000000000000000)
  dδ := (1493142344314589767262369/12500000000000000000000000)
  dM := (15761712868859077338323793/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(51177002666632862570850193/10000000000000000000000000), (32593272462498489971949311/1000000000000000000000000)]
  retention := ![(3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1733/3648)
  hi := (869/1824)
  vmin := (3318695/13307904)
  damping := (3318695/13307904)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell039
