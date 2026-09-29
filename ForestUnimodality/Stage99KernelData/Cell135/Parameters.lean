import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 122
  A := (2174000622421329498479281/20000000000000000000000000)
  B := (2964969393288325542196171/31250000000000000000000000)
  C := (34626890263833848271346483/50000000000000000000000000)
  dδ := (14937447775891019019489647/100000000000000000000000000)
  dM := (16414280907104019779224613/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(2747373027611232032541011/400000000000000000000000), (40134184867841531385579401/10000000000000000000000000), (26003421931824753698947461/1000000000000000000000000), (19894922758499713921764851/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (47737/90312)
  hi := (31833/60208)
  vmin := (903261375/3625003264)
  damping := (903261375/3625003264)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell135
