import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell170
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 41
  A := (5630394040692334355355797/1000000000000000000000000)
  B := (-4393578845472764261848031/62500000000000000000000000)
  C := (10359054805480395755612477/50000000000000000000000000)
  dδ := (1280163104614983893281277/20000000000000000000000000)
  dM := 0
  wL := 0
  wR := 1
  wC := 0
  price := ![(15587494358178908271383989/2500000000000000000000000), (25579525002049585680197197/10000000000000000000000000), (42613905386733357261164201/10000000000000000000000000), (95699449291879368217905721/10000000000000000000000000)]
  retention := ![(19/20), (7/10), (1/4), (1/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (653/1128)
  hi := (7/12)
  vmin := (35/144)
  damping := (35/144)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell170
