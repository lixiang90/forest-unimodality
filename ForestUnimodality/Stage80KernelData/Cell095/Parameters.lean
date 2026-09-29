import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 39
  A := (-2710728174509456383844963/25000000000000000000000000)
  B := (88105413668370172186605771/1000000000000000000000000000)
  C := (33559522600134705436203397/10000000000000000000000000000)
  dδ := (5967759907001944641447011/50000000000000000000000000)
  dM := (3988918279653645877769197/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(58611430580823036251558733/10000000000000000000000000), (32914438569057139716278471/1000000000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (26/51)
  hi := (3579/7004)
  vmin := (12258075/49056016)
  damping := (12258075/49056016)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell095
