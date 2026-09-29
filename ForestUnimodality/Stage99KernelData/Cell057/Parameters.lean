import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 57
  A := (1476436270220557385215443/4000000000000000000000000)
  B := (41975613763030890368543879/1000000000000000000000000000)
  C := (-15752695069786248438341303/100000000000000000000000000000)
  dδ := (83390581857102130669545659/1000000000000000000000000000)
  dM := (81235469425801993745284157/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(53009201107447161405161751/10000000000000000000000000), (570747344739797490831279/400000000000000000000000), (2530853945086664058550241/1250000000000000000000000), (6066676797996424674863647/125000000000000000000000)]
  retention := ![(4/5), (3/5), (1/2), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (131/264)
  hi := (197/396)
  vmin := (17423/69696)
  damping := (17423/69696)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell057
