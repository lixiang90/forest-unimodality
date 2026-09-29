import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 78
  A := (-18570656275199849432944177/25000000000000000000000000)
  B := (72436724414426001406042133/1000000000000000000000000000)
  C := (-398069764774193566442273/1562500000000000000000000)
  dδ := (1720608155843967928752547/31250000000000000000000000)
  dM := (77866062907256013148060703/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(58173780304006745822675839/10000000000000000000000000), (28382233860552211979211279/1000000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4/9)
  hi := (301/666)
  vmin := (20/81)
  damping := (20/81)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell026
