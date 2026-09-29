import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 23
  A := (17683736652918203736462033/100000000000000000000000000)
  B := (16769648246685951026302419/500000000000000000000000000)
  C := (-80872299728122029605081877/1000000000000000000000000000)
  dδ := (37425695327348983132420557/1000000000000000000000000000)
  dM := (10781810489363149031631639/25000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(95862353861164406598760479/100000000000000000000000000), (73077689701165233771007479/10000000000000000000000000)]
  retention := ![(3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (89/255)
  hi := (91/255)
  vmin := (14774/65025)
  damping := (14774/65025)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell013
