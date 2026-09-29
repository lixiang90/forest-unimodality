import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 42
  A := (9046475890186678520166197/5000000000000000000000000)
  B := (-17202093600362823588856287/2000000000000000000000000000)
  C := (-4786335787407452677100217/2000000000000000000000000000)
  dδ := (10925687145253326626459511/100000000000000000000000000)
  dM := (59180565856124984786684751/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(8171016166730379337579393/1250000000000000000000000), (44559931360587743398582461/5000000000000000000000000), (14126821134488325881761739/500000000000000000000000)]
  retention := ![(4/5), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4631/9506)
  hi := (9287/19012)
  vmin := (22576125/90364036)
  damping := (22576125/90364036)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell061
