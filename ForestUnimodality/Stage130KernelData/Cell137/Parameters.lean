import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 88
  A := (-3891893799789757193963169/2500000000000000000000000)
  B := (48613343326638247532400783/500000000000000000000000000)
  C := (8673175157158817191738187/2000000000000000000000000000)
  dδ := (15750970801369081758513957/250000000000000000000000000)
  dM := (65042050513034881413163/62500000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(1246076534866696228220917/100000000000000000000000), (12148210560858041517917627/12500000000000000000000000), (17340628282817203142940343/1000000000000000000000000), (3475708419256523296070327/62500000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11791/22366)
  hi := (23607/44732)
  vmin := (498697875/2000951824)
  damping := (498697875/2000951824)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell137
