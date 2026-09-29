import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 39
  A := (28212272459090454891139643/100000000000000000000000000)
  B := (15231750438846041600937653/250000000000000000000000000)
  C := (39355590630845592101105801/5000000000000000000000000000)
  dδ := (3001648702865406664885839/25000000000000000000000000)
  dM := (15213524321946879282879683/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(76176760601962909547069103/10000000000000000000000000), (10007668833920646989099623/500000000000000000000000), (11536924166564869409512539/1000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (47887/90312)
  hi := (31933/60208)
  vmin := (902905575/3625003264)
  damping := (902905575/3625003264)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell164
