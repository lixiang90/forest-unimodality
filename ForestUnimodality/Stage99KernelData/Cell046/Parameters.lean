import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 54
  A := (17827143637462254916137283/25000000000000000000000000)
  B := (8059348949037113685189837/250000000000000000000000000)
  C := (-31153547834064905866502393/10000000000000000000000000000)
  dδ := (89282308279591451882772901/1000000000000000000000000000)
  dM := (39441481667491686945864471/50000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(56735669868526299453037609/10000000000000000000000000), (35679904196627765244898001/10000000000000000000000000), (9077074277098573418243177/200000000000000000000000)]
  retention := ![(4/5), (9/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (8999/18624)
  hi := (47/97)
  vmin := (86615375/346853376)
  damping := (86615375/346853376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell046
