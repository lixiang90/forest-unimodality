import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell190
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 74
  A := (-2135945552764984740878873/1250000000000000000000000)
  B := (5924213621080706704269403/50000000000000000000000000)
  C := (26437502881684286221153357/5000000000000000000000000000)
  dδ := (35787025291045243546861343/500000000000000000000000000)
  dM := (14448377102417744952816969/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(26404044883116863928762541/5000000000000000000000000), (319950383531812931892091/39062500000000000000000), (58753428212744459813166031/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
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
end ForestUnimodality.Stage130KernelData.Cell190
