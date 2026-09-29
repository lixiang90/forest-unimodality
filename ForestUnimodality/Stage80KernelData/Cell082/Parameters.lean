import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 44
  A := (125667054319689422277051/125000000000000000000000)
  B := (5643033070649521032446927/200000000000000000000000000)
  C := (-2000588740577550486091779/20000000000000000000000000000)
  dδ := (164392464004877217852163/1562500000000000000000000)
  dM := (24939593105679439943161979/25000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(52626410009644750687129999/10000000000000000000000000), (19387733962552877731155831/10000000000000000000000000), (37698820889809880441134737/1000000000000000000000000)]
  retention := ![(4/5), (9/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (197/396)
  hi := (395/792)
  vmin := (39203/156816)
  damping := (39203/156816)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell082
