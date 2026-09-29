import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 41
  A := (20484450341476697177256483/10000000000000000000000000)
  B := (-22616988761918470351997001/1000000000000000000000000000)
  C := (-592673748342601239280647/400000000000000000000000000)
  dδ := (11401324824682997072233803/100000000000000000000000000)
  dM := (10179435644775760314104801/25000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(66778640042250181352301297/10000000000000000000000000), (36258059466050319485930231/1000000000000000000000000)]
  retention := ![(4/5), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (49/99)
  hi := (131/264)
  vmin := (2450/9801)
  damping := (2450/9801)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell078
