import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 51
  A := (-67296446809965697720912203/100000000000000000000000000)
  B := (58746957056286562906533/625000000000000000000000)
  C := (43982020890592240071684249/100000000000000000000000000000)
  dδ := (45758531966756735287482627/500000000000000000000000000)
  dM := (619401915881984208717137/400000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(5753565796841852986176491/1000000000000000000000000), (14764501148071718095167171/10000000000000000000000000), (3502370207279333413907807/200000000000000000000000), (1274705067006501657544959/50000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (405/808)
  hi := (203/404)
  vmin := (40803/163216)
  damping := (40803/163216)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell062
