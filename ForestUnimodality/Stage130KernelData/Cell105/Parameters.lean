import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 74
  A := (-2962566591354060510070667/2000000000000000000000000)
  B := (10833460845837300512428669/100000000000000000000000000)
  C := (4127624641180332879311643/1250000000000000000000000000)
  dδ := (72318370072442517138000539/1000000000000000000000000000)
  dM := (6643337454733079993837719/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(60072210242424279869055681/10000000000000000000000000), (14583402007932088295660833/2000000000000000000000000), (29575394202863613202225679/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (27/52)
  hi := (22597/43472)
  vmin := (471712375/1889814784)
  damping := (471712375/1889814784)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell105
