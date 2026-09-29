import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 91
  A := (-13636369272386587481094011/10000000000000000000000000)
  B := (86461913391277400720014157/1000000000000000000000000000)
  C := (-10330393294847296206846743/100000000000000000000000000000)
  dδ := (60373956328854602726430301/1000000000000000000000000000)
  dM := (45143219121569831513152149/50000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(12386371965996366029116871/1000000000000000000000000), (38594865227184534717252973/500000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (395/792)
  hi := (1/2)
  vmin := (156815/627264)
  damping := (156815/627264)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell067
