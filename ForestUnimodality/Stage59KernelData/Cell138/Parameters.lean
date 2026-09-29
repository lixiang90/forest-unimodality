import ForestUnimodality.FiniteMarginalParameters
import ForestUnimodality.FiniteMarginalGeometry
import ForestUnimodality.FiniteKernelRationalCertificate

namespace ForestUnimodality.Stage59KernelData.Cell138
open FiniteMarginalSupport FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def parameters : Parameters where
  lowerOrder := 59
  cap := 79
  lowerRank := 17
  upperRank := 22
  density := (285040520214071060750346477627 / 1000000000000000000000000000000)
  probabilityCap := (27 / 52)

def pairs : List (ℕ × ℕ) := [(59, 17), (59, 18), (59, 19), (59, 20), (59, 21), (59, 22), (60, 18), (60, 19), (60, 20), (60, 21), (60, 22), (61, 18), (61, 19), (61, 20), (61, 21), (61, 22), (62, 18), (62, 19), (62, 20), (62, 21), (62, 22), (63, 18), (63, 19), (63, 20), (63, 21), (63, 22), (64, 19), (64, 20), (64, 21), (64, 22), (65, 19), (65, 20), (65, 21), (65, 22), (66, 19), (66, 20), (66, 21), (66, 22), (67, 20), (67, 21), (67, 22), (68, 20), (68, 21), (68, 22), (69, 20), (69, 21), (69, 22), (70, 20), (70, 21), (70, 22), (71, 21), (71, 22), (72, 21), (72, 22), (73, 21), (73, 22), (74, 22), (75, 22), (76, 22), (77, 22)]
theorem pairs_checked : parameters.pairs = pairs := by decide +kernel

def activityLower : ℚ := (22331 / 20725)
def activityUpper : ℚ := (27 / 25)

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (26)
  A := (2607676461850022471168131 / 1000000000000000000000000)
  B := (-4430644984051250456769111 / 100000000000000000000000000)
  C := (541621049367879137115267 / 5000000000000000000000000)
  dδ := (274464041044662654389441 / 2000000000000000000000000)
  dM := (3287919212680565149257983 / 5000000000000000000000000000)
  wL := (546792282519 / 312500000000)
  wR := (5625661739847 / 2500000000000)
  wC := (1 / 10000000000000)
  price := ![(3146842106864831567492047 / 500000000000000000000000)]
  retention := ![(4 / 5)]
  fixedIndices := {-1, 0, 1, 2, 3, 4, 5}
  fixedPrice := fun j => if j = -1 then (484614342085642846313931 / 20000000000000000000000) else if j = 0 then (1168721515804552169015551 / 50000000000000000000000) else if j = 1 then (3278010655248129978645011 / 100000000000000000000000) else if j = 2 then (3514248548930919469057699 / 100000000000000000000000) else if j = 3 then (1520684925348615657014761 / 100000000000000000000000) else if j = 4 then (1165707655879841375679007 / 100000000000000000000000) else if j = 5 then (690675255770740381677797 / 50000000000000000000000) else 0

def countBound : ℤ → ℚ := fun j => if j = -1 then (26869762277070123503673873 / 1000000000000000000000000000000) else if j = 0 then (442526975791539162189319 / 10000000000000000000000000000) else if j = 1 then (37576409227386447707671973 / 500000000000000000000000000000) else if j = 2 then (115976571689464344776765349 / 1000000000000000000000000000000) else if j = 3 then (139601428885466340934995327 / 1000000000000000000000000000000) else if j = 4 then (139601428885466340934995327 / 1000000000000000000000000000000) else if j = 5 then (139601428885466340934995327 / 1000000000000000000000000000000) else 0

def interval : IntervalWitness where
  lo := (22331 / 43056)
  hi := (27 / 52)
  vmin := (675 / 2704)
  damping := (675 / 2704)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms pairs_checked
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage59KernelData.Cell138
