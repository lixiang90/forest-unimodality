import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 88
  A := (-3918152816239995175884303/2500000000000000000000000)
  B := (97764136079026953130011179/1000000000000000000000000000)
  C := (44282136333244131662367771/10000000000000000000000000000)
  dδ := (12611734462548188084873857/200000000000000000000000000)
  dM := (5235758242943461867463517/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(6175824043516366934625239/500000000000000000000000), (2844915261135168571549059/2500000000000000000000000), (3330205956396176958378419/200000000000000000000000), (56233474441358161755033507/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23607/44732)
  hi := (94453/178928)
  vmin := (7978917175/32015229184)
  damping := (7978917175/32015229184)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell139
