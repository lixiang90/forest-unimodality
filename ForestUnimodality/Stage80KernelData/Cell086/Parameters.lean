import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 43
  A := (2381905921236677901049461/2000000000000000000000000)
  B := (1030941991825030804377783/62500000000000000000000000)
  C := 0
  dδ := (10318508551613371493349547/100000000000000000000000000)
  dM := (82151257864648548172314957/100000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(55330326095246480377909393/10000000000000000000000000), (4942009617262572152007749/2500000000000000000000000), (18288970709337533548932697/500000000000000000000000)]
  retention := ![(4/5), (2/5), (1/10)]
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
end ForestUnimodality.Stage80KernelData.Cell086
