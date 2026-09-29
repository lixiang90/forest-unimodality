import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell240
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 20
  A := (15424330496700567772805357/100000000000000000000000000)
  B := (6010992159992246605670907/250000000000000000000000000)
  C := (8890346889889498560588521/200000000000000000000000000)
  dδ := (1022382818320827779778881/40000000000000000000000000)
  dM := (6104878118901900583941067/25000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(26313709370681852561801861/10000000000000000000000000), (19956663007251997932200993/5000000000000000000000000)]
  retention := ![(7/10), (3/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (35/52)
  hi := (53/78)
  vmin := (1325/6084)
  damping := (13250000000000000000000000000000000000000000/150116682940569144593175659726526589679581089)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell240
