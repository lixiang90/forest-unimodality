import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell200
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 53
  A := (43077812106809297060294739/5000000000000000000000000)
  B := (-5489563345038547120813277/50000000000000000000000000)
  C := (40673033820540333005411071/100000000000000000000000000)
  dδ := (11831751105296216264317621/100000000000000000000000000)
  dM := (150444602501777430561547/400000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(91432491162812983276353407/10000000000000000000000000), (39534728778406980076454147/10000000000000000000000000), (6960444892977515785048581/500000000000000000000000), (9256936695164039718974891/2000000000000000000000000)]
  retention := ![(19/20), (7/10), (1/5), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (5/9)
  hi := (116/207)
  vmin := (10556/42849)
  damping := (10556/42849)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell200
