import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell134.Parameters
import ForestUnimodality.BinomialMassData.Q95449_180624.Batch000_049
import ForestUnimodality.BinomialMassData.Q95449_180624.Batch050_099
import ForestUnimodality.BinomialMassData.Q95449_180624.Batch100_149
import ForestUnimodality.BinomialMassData.Q47737_90312.Batch000_049
import ForestUnimodality.BinomialMassData.Q47737_90312.Batch050_099
import ForestUnimodality.BinomialMassData.Q47737_90312.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree000.table
  base := (5715298661658442462950802087/100000000000000000000000000)
  polynomial :=
    { denominator := 602080000000000000000000000000000000000000000
      center := (3913409)
      previous := (0)
      next := (3492175)
      square := (90597450446357259190577337715200000000000000)
      linear := (-420488388240465858096683861302400000000000000)
      constant := (34410670182113150380934189205409600000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree000.table
  base := (5715298661658442462950802087/100000000000000000000000000)
  polynomial :=
    { denominator := 301040000000000000000000000000000000000000000
      center := (1957217)
      previous := (0)
      next := (1745575)
      square := (45298725223178629595288668857600000000000000)
      linear := (-210244194120232929048341930651200000000000000)
      constant := (17205335091056575190467094602704800000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree001.table
  base := (85923045167052086647532868694719427788631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-5827822920803413326113641148690059200000000000000)
      constant := (236397542502077745151101030735916836623499757818688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree001.table
  base := (171816375339118875262398325425061198123103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-971351006306009698758101950478403200000000000000)
      constant := (39392992547924425830243290674817721312249940550512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24959129473215556711/50000000000000000000)
  directionHi := (49918258946431113423/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree002.table
  base := (215913091174840448770574123913837467157473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-2302917475586735860057939395712441600000000000000)
      constant := (50970958077908966951124057817037317375708276686992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree002.table
  base := (4316932709199681666759626556934210717507/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-3454659330412748656521879647749022400000000000000)
      constant := (76434808810371864423793817119144653969812454419600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24959129473215556711/50000000000000000000)
  centralHi := (49918258946431113423/100000000000000000000)
  directionLo := (35297539406047483679/50000000000000000000)
  directionHi := (70595078812094967359/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree003.table
  base := (71322536474317544289970756292415270388279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-2663227310905667278077998408528196800000000000000)
      constant := (35683313261995437470606064453445122450119240292832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree003.table
  base := (1782352461916473764800251970583350354273/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-1331755213969156072256484481354278400000000000000)
      constant := (17835766592967371158633578440588771045737953367680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35297539406047483679/50000000000000000000)
  centralHi := (70595078812094967359/100000000000000000000)
  directionLo := (4323048036029917191/5000000000000000000)
  directionHi := (86460960720598343821/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree004.table
  base := (49642450895471537406217794054268643765089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-9070611438673796088294172264031856000000000000000)
      constant := (82086220154163398105443208581985019242987827843936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree004.table
  base := (24810090932301656649709067343849593349483/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-1511957317800729259005675746792216000000000000000)
      constant := (13676828382693292455174849512835666477118570964064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4323048036029917191/5000000000000000000)
  centralHi := (86460960720598343821/100000000000000000000)
  directionLo := (19967303578572445369/20000000000000000000)
  directionHi := (49918258946431113423/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree005.table
  base := (72510001108865278433900879270615952704123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-3383846981543530114118116434159707200000000000000)
      constant := (22988839468951718771525901123971537740182218828592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree005.table
  base := (36238000675372230247249955598945983229997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-5076478264896907337264601036690460800000000000000)
      constant := (34475217496009813240702109262683606031580322695664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19967303578572445369/20000000000000000000)
  centralHi := (49918258946431113423/50000000000000000000)
  directionLo := (22324124064531400529/20000000000000000000)
  directionHi := (55810310161328501323/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree006.table
  base := (11016128446692589391482634804861924309153/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-3744156816862461532138175446975462400000000000000)
      constant := (20923359011226111105916285118992095390625178148560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree006.table
  base := (55054473302966125659953496905571663910801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-1872361525463875632504058277668091200000000000000)
      constant := (10460269847141472198287746449201204820705144682952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22324124064531400529/20000000000000000000)
  centralHi := (55810310161328501323/50000000000000000000)
  directionLo := (24454852653375525389/20000000000000000000)
  directionHi := (61137131633438813473/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree007.table
  base := (43042008721818357967565920516327377230013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-12313399956544178850474703379373652800000000000000)
      constant := (60808854313239626595088905595576633853379325705456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree007.table
  base := (10755324470656695679717045913475802057327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-2052563629295448819253249543106028800000000000000)
      constant := (10134451394305057617762611483731308405353536264416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24454852653375525389/20000000000000000000)
  centralHi := (61137131633438813473/50000000000000000000)
  directionLo := (132071299053581846931/100000000000000000000)
  directionHi := (33017824763395461733/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree008.table
  base := (4277098804230564714674014561871907399807/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-4464776487500324368178293472606972800000000000000)
      constant := (20534319475728283950322015533654013137103063985024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree008.table
  base := (34199782275577098156205951934384151866281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-6698297199381066018007322425631899200000000000000)
      constant := (30803115305855518324528637029477940032356904675736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132071299053581846931/100000000000000000000)
  centralHi := (33017824763395461733/25000000000000000000)
  directionLo := (141190157624189934717/100000000000000000000)
  directionHi := (70595078812094967359/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree009.table
  base := (6848053773513181241743683707260816561599/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-4825086322819255786198352485422728000000000000000)
      constant := (21442694159100383287429671721889200283775408014784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree009.table
  base := (13688858576837866038227318299475121826007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-2412967836958595192751632073981904000000000000000)
      constant := (10722710258482955039073392227065221081629563442928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141190157624189934717/100000000000000000000)
  centralHi := (70595078812094967359/50000000000000000000)
  directionLo := (37438694209823335067/25000000000000000000)
  directionHi := (149754776839293340269/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree010.table
  base := (10940519829158896917292917390590219318331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-15556188474414561612655234494715449600000000000000)
      constant := (68517115536441940345457091952275356468284648762144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree010.table
  base := (21868282974102577473732932317526816038627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-2593169940790168379500823339419841600000000000000)
      constant := (11421663017507720796043244916133367017110950783704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37438694209823335067/25000000000000000000)
  centralHi := (149754776839293340269/100000000000000000000)
  directionLo := (157855395100799449801/100000000000000000000)
  directionHi := (78927697550399724901/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree011.table
  base := (2160510752772660605002114717760777919509/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-5545705993457118622238470511054238400000000000000)
      constant := (24632913664145375929233700391558395914699627138688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree011.table
  base := (4318147877471560114875610276439665872897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-8320116133865224698750043814573337600000000000000)
      constant := (36958130344133803042202810148345755858120387800928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157855395100799449801/100000000000000000000)
  centralHi := (78927697550399724901/50000000000000000000)
  directionLo := (82780067556556827251/50000000000000000000)
  directionHi := (165560135113113654503/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree012.table
  base := (3340375028461492922692596729517449383817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-5906015828776050040258529523869993600000000000000)
      constant := (26769977628022781001145530501208708590322853444672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree012.table
  base := (6675487860307655902636407405619628357481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-2953574148453314752999205870295716800000000000000)
      constant := (13388701743725952619517804069355562196145973988624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82780067556556827251/50000000000000000000)
  centralHi := (165560135113113654503/100000000000000000000)
  directionLo := (172921921441196687641/100000000000000000000)
  directionHi := (86460960720598343821/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree013.table
  base := (9962728159540317508192821208471366919309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-18798976992284944374835765610057246400000000000000)
      constant := (87648361601089334972273246048879753037444390554608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree013.table
  base := (4976498682676083965846364598188987330751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-3133776252284887939748397135733654400000000000000)
      constant := (14612596057225859865657849683229662972676688910704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172921921441196687641/100000000000000000000)
  centralHi := (86460960720598343821/50000000000000000000)
  directionLo := (179982842213246395383/100000000000000000000)
  directionHi := (22497855276655799423/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree014.table
  base := (698824912287184468163877519414719176591/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-6626635499413912876298647549501504000000000000000)
      constant := (31948794626056405765343063637366404140491104620640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree014.table
  base := (6979204190166978522340438191338920875489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-9941935068349383379492765203514776000000000000000)
      constant := (47939380908279112783338691082237572540989252743384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179982842213246395383/100000000000000000000)
  centralHi := (22497855276655799423/12500000000000000000)
  directionLo := (186777022321808360373/100000000000000000000)
  directionHi := (93388511160904180187/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree015.table
  base := (546064331667296385709889521043825286457/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-6986945334732844294318706562317259200000000000000)
      constant := (34952242842754149184663783898012803425226179997824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree015.table
  base := (4360087365967508707155102539056882398093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-3494180459948034313246779666609529600000000000000)
      constant := (17482420426191980507100909908609122942960977261736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186777022321808360373/100000000000000000000)
  centralHi := (93388511160904180187/50000000000000000000)
  directionLo := (96666292785598549103/50000000000000000000)
  directionHi := (193332585571197098207/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree016.table
  base := (2052237850186930358315431338398753183567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-22041765510155327137016296725399043200000000000000)
      constant := (114644536454625910661173518656642096054492643655504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree016.table
  base := (1022190923982582064586915222568788354463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-3674382563779607499995970932047467200000000000000)
      constant := (19114669053938696080685561330520768915590847747952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96666292785598549103/50000000000000000000)
  centralHi := (193332585571197098207/100000000000000000000)
  directionLo := (19967303578572445369/10000000000000000000)
  directionHi := (199673035785724453691/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree017.table
  base := (-219462360954591912894686742892258277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-7707565005370707130358824587948769600000000000000)
      constant := (41727622020133869797681858267473287927184096498992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree017.table
  base := (-7538987096085561939194973657325393603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-11563754002833542060235486592456214400000000000000)
      constant := (62616151685626639664883328907769394084126160026232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19967303578572445369/10000000000000000000)
  centralHi := (199673035785724453691/100000000000000000000)
  directionLo := (41163650856613847339/20000000000000000000)
  directionHi := (25727281785383654587/12500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree018.table
  base := (-1820663412233482771705645092708182287219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-8067874840689638548378883600764524800000000000000)
      constant := (45483366366182665231727823049039632538082758719824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree018.table
  base := (-913737749212778667371182163534956551187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-4034786771442753873494353462923342400000000000000)
      constant := (22750962562317214852732718845600522045240558870352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41163650856613847339/20000000000000000000)
  centralHi := (25727281785383654587/12500000000000000000)
  directionLo := (52946309109071225519/25000000000000000000)
  directionHi := (211785236436284902077/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree019.table
  base := (-34353387383189768074565918388277512893/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-25284554028025709899196827840740840000000000000000)
      constant := (148428397332040132582806737459143217882970117198400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree019.table
  base := (-860417436631159586822272122641019625603/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-4214988875274327060243544728361280000000000000000)
      constant := (24748432319170838038860660887368887644612633378976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52946309109071225519/25000000000000000000)
  centralHi := (211785236436284902077/100000000000000000000)
  directionLo := (108794323092494178153/50000000000000000000)
  directionHi := (217588646184988356307/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree020.table
  base := (-608291773635419766716263059907641511207/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-8788494511327501384419001626396035200000000000000)
      constant := (53700915767045591673238663951251949991666366210176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree020.table
  base := (-243610466714779237576373685784407873567/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-13185572937317700740978207981397652800000000000000)
      constant := (80585873156751628237805810553639541733773110644960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108794323092494178153/50000000000000000000)
  centralHi := (217588646184988356307/100000000000000000000)
  directionLo := (22324124064531400529/10000000000000000000)
  directionHi := (223241240645314005291/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree021.table
  base := (-11977529419553211516696051088810149231/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-9148804346646432802439060639211790400000000000000)
      constant := (58153446693542258155804444467933739115161533120512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree021.table
  base := (-1227587815580045913325362472850350475749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-4575393082937473433741927259237155200000000000000)
      constant := (29089403995303325078746807381504335922166550336760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22324124064531400529/10000000000000000000)
  centralHi := (223241240645314005291/100000000000000000000)
  directionLo := (7148568755700848043/3125000000000000000)
  directionHi := (228754200182427137377/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree022.table
  base := (-453127997084985657308219812183952637191/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-28527342545896092661377358956082636800000000000000)
      constant := (188490146647567183889794904824902743565283651625728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree022.table
  base := (-725508528989876427503249722689722313087/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-4755595186769046620491118524675092800000000000000)
      constant := (31428933009704391964784974116747334198689373463760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7148568755700848043/3125000000000000000)
  centralHi := (228754200182427137377/100000000000000000000)
  directionLo := (117068694232643700467/50000000000000000000)
  directionHi := (46827477693057480187/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree023.table
  base := (-4116525860518862853217404619676484995969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-9869424017284295638479178664843300800000000000000)
      constant := (67727537120579283604853052421460919658195668519648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree023.table
  base := (-164754130437621749609519817927004300743/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-14807391871801859421720929370339091200000000000000)
      constant := (101636856571167433822028474188502366825302753319600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117068694232643700467/50000000000000000000)
  centralHi := (46827477693057480187/20000000000000000000)
  directionLo := (47879911968836303431/20000000000000000000)
  directionHi := (59849889961045379289/25000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree024.table
  base := (-454686949566787460863360127566739809721/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-10229733852603227056499237677659056000000000000000)
      constant := (72843139951004746502243429352425856164903295088320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree024.table
  base := (-4549017482956309269685677506212639757593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-5115999394432192993989501055550968000000000000000)
      constant := (36438075858102488629278804445395170737541825388528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47879911968836303431/20000000000000000000)
  centralHi := (59849889961045379289/25000000000000000000)
  directionLo := (244548526533755253891/100000000000000000000)
  directionHi := (61137131633438813473/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree025.table
  base := (-4921392594887774841930805313640800760433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-31770131063766475423557890071424433600000000000000)
      constant := (234523316161578703209556491902626953819946259855008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree025.table
  base := (-196934909245726944570769214289693984511/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-5296201498263766180738692320988905600000000000000)
      constant := (39105094752503650072552580001297739788416343056400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244548526533755253891/100000000000000000000)
  centralHi := (61137131633438813473/25000000000000000000)
  directionLo := (249591294732155567113/100000000000000000000)
  directionHi := (124795647366077783557/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree026.table
  base := (-2622381754628781622790206104380908311139/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-10950353523241089892539355703290566400000000000000)
      constant := (83719318080656388331796280663796754468209099360576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree026.table
  base := (-2623293496064899966792417032330270583273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-16429210806286018102463650759280529600000000000000)
      constant := (125636853845759409503462571881923614053612071698848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249591294732155567113/100000000000000000000)
  centralHi := (124795647366077783557/50000000000000000000)
  directionLo := (254534176452429855697/100000000000000000000)
  directionHi := (127267088226214927849/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree027.table
  base := (-11042143827033882375289098192509559722661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-11310663358560021310559414716106321600000000000000)
      constant := (89475924895860193811874469913692768153384433764656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree027.table
  base := (-5522749516253225798170575480500953686551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-5656605705926912554237074851864780800000000000000)
      constant := (44758718974737255771752936631241953558196237006096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254534176452429855697/100000000000000000000)
  centralHi := (127267088226214927849/50000000000000000000)
  directionLo := (129691441080897515731/50000000000000000000)
  directionHi := (259382882161795031463/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree028.table
  base := (-719238157395661590406033260754144776559/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-35012919581636858185738421186766230400000000000000)
      constant := (286327900802139936695078496685466122250335222934272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree028.table
  base := (-11510894570117247901293270944825908409043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-5836807809758485740986266117302718400000000000000)
      constant := (47743585154717935449633693790756279690795439933864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129691441080897515731/50000000000000000000)
  centralHi := (259382882161795031463/100000000000000000000)
  directionLo := (264142598107163693863/100000000000000000000)
  directionHi := (33017824763395461733/12500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree029.table
  base := (-297320695732145039849584456209162231529/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-12031283029197884146599532741737832000000000000000)
      constant := (101618016683230890058343994142012834760004628223360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree029.table
  base := (-11895660331361988348406994568348697224401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-18051029740770176783206372148221968000000000000000)
      constant := (152498508538339487752632237425221576612943621989544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264142598107163693863/100000000000000000000)
  centralHi := (33017824763395461733/12500000000000000000)
  directionLo := (53763610262349587463/20000000000000000000)
  directionHi := (67204512827936984329/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree030.table
  base := (-12202734138608469316202882910897792878721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-12391592864516815564619591754553587200000000000000)
      constant := (108000819353356854156648688312028305977765026178416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree030.table
  base := (-6102666827553471271466908077731457998891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-6197212017421632114484648648178593600000000000000)
      constant := (54025844771689684007404697107163806689908826038736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53763610262349587463/20000000000000000000)
  centralHi := (67204512827936984329/25000000000000000000)
  directionLo := (273413564563443883307/100000000000000000000)
  directionHi := (68353391140860970827/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree031.table
  base := (-497696076042150247974745600727849776291/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-38255708099507240947918952302108027200000000000000)
      constant := (343769813083700268300903629377162222643328696185200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree031.table
  base := (-12444785940627001819496790329890556055871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-6377414121253205301233839913616531200000000000000)
      constant := (57322059092751508209176363648881044697959145582408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273413564563443883307/100000000000000000000)
  centralHi := (68353391140860970827/25000000000000000000)
  directionLo := (138966551608230034821/50000000000000000000)
  directionHi := (277933103216460069643/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree032.table
  base := (-12616121114585304414755143607657024970977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-13112212535154678400659709780185097600000000000000)
      constant := (121384399753321798625289178087746010117979929358192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree032.table
  base := (-12618306132370677051640514208407988551773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-19672848675254335463949093537163406400000000000000)
      constant := (182162979855618564950151737319625531067763897688712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138966551608230034821/50000000000000000000)
  centralHi := (277933103216460069643/100000000000000000000)
  directionLo := (56476063049675973887/20000000000000000000)
  directionHi := (70595078812094967359/25000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree033.table
  base := (-6363835874744876833332468487900650540501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-13472522370473609818679768793000852800000000000000)
      constant := (128383349129332800985132048554767204410370063850592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree033.table
  base := (-12729673162971080563162956529757818519901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-6737818328916351674732222444492406400000000000000)
      constant := (64222219266455928446019647806567706585494975813848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56476063049675973887/20000000000000000000)
  centralHi := (70595078812094967359/25000000000000000000)
  directionLo := (286758565723880943143/100000000000000000000)
  directionHi := (35844820715485117893/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree034.table
  base := (-6390193360997136768865137223353214865163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-41498496617377623710099483417449824000000000000000)
      constant := (406758092124261390482766318648516996358334051915488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree034.table
  base := (-12782218937505991522346606530159947335239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-6918020432747924861481413709930344000000000000000)
      constant := (67825359593788782107743093850354195589615328836872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286758565723880943143/100000000000000000000)
  centralHi := (35844820715485117893/12500000000000000000)
  directionLo := (58214193318214174629/20000000000000000000)
  directionHi := (145535483295535436573/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree035.table
  base := (-1277720673233662054640299301970101336581/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-14193142041111472654719886818632363200000000000000)
      constant := (142991778236587266592945276987626258890301945249760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree035.table
  base := (-12778883179451257847378121630974739812607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-21294667609738494144691814926104844800000000000000)
      constant := (214590243754064697331107041890546324688538957186008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58214193318214174629/20000000000000000000)
  centralHi := (145535483295535436573/50000000000000000000)
  directionLo := (29532040256051264953/10000000000000000000)
  directionHi := (295320402560512649531/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree036.table
  base := (-6360364040450969637992606394732966864871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-14553451876430404072739945831448118400000000000000)
      constant := (150600003489997555682977679291545348138304847257632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree036.table
  base := (-3180565313104134749083429263581365491111/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-7278424640411071234979796240806219200000000000000)
      constant := (75336090232855645630226947166646340620643207751712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29532040256051264953/10000000000000000000)
  centralHi := (295320402560512649531/100000000000000000000)
  directionLo := (37438694209823335067/12500000000000000000)
  directionHi := (299509553678586680537/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree037.table
  base := (-12613244409396214185803528292868945030093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-44741285135248006472280014532791620800000000000000)
      constant := (475230560443953247256796905551635641339064305645584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree037.table
  base := (-6307322952530115849551936865525822758983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-7458626744242644421728987506244156800000000000000)
      constant := (79243126812623202299602520967971172113900071229968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37438694209823335067/12500000000000000000)
  centralHi := (299509553678586680537/100000000000000000000)
  directionLo := (75910228774268765403/25000000000000000000)
  directionHi := (303640915097075061613/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree038.table
  base := (-6228391588360740235135864912513900637373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-15274071547068266908780063857079628800000000000000)
      constant := (166421868863976752836059590640475019468018899326816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree038.table
  base := (-194657246081537003797032474520396836873/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-22916486544222652825434536315046283200000000000000)
      constant := (249752884239986412536016914683621307790560596679168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75910228774268765403/25000000000000000000)
  centralHi := (303640915097075061613/100000000000000000000)
  directionLo := (76929203613302835217/25000000000000000000)
  directionHi := (307716814453211340869/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree039.table
  base := (-2450627512897142989516103703946491813/2000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-15634381382387198326800122869895384000000000000000)
      constant := (174634643369900700638460944024807446867664288240000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree039.table
  base := (-12254307166492910993684730236700658282603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-7819030951905790795227370037120032000000000000000)
      constant := (87359390991561281044804342422315015110456734080744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76929203613302835217/25000000000000000000)
  centralHi := (307716814453211340869/100000000000000000000)
  directionLo := (311739427203995237373/100000000000000000000)
  directionHi := (155869713601997618687/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree040.table
  base := (-3000973602568425238195907856761658386717/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-47984073653118389234460545648133417600000000000000)
      constant := (549144452442626725453477348056525231908573425566784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree040.table
  base := (-480198489667424317226477130157965331571/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-7999233055737363981976561302557969600000000000000)
      constant := (91568235873489904234913742495454946841762720900200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311739427203995237373/100000000000000000000)
  centralHi := (155869713601997618687/50000000000000000000)
  directionLo := (315710790201598899603/100000000000000000000)
  directionHi := (78927697550399724901/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree041.table
  base := (-5855229342287321090903101419760527337699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-16355001053025061162840240895526894400000000000000)
      constant := (191662072882988302181998514415694490337809986843808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree041.table
  base := (-5855716619593361866197050199267749374651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-24538305478706811506177257703987721600000000000000)
      constant := (287632010946437937331762706414964424345054281151088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315710790201598899603/100000000000000000000)
  centralHi := (78927697550399724901/25000000000000000000)
  directionLo := (19977050859396387489/6250000000000000000)
  directionHi := (12785312550013687993/4000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree042.table
  base := (-11374074957086876914613173835390718447023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-16715310888343992580860299908342649600000000000000)
      constant := (200476127603162709745963573139480089732139788369808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree042.table
  base := (-11374964068212841822603284675090028611611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-8359637263400510355474943833433844800000000000000)
      constant := (100286553405811685840765800013554699237158023021928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19977050859396387489/6250000000000000000)
  centralHi := (12785312550013687993/4000000000000000000)
  directionLo := (64701458469559678247/20000000000000000000)
  directionHi := (80876823086949597809/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree043.table
  base := (-10995846238033318437353341710945794487303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-51226862170988771996641076763475214400000000000000)
      constant := (628470195221260464898560684785209456460585015958064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree043.table
  base := (-5498328561333893554784338428044038055017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-8539839367232083542224135098871782400000000000000)
      constant := (104795760263815162581867292830575927807176447714032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64701458469559678247/20000000000000000000)
  centralHi := (80876823086949597809/25000000000000000000)
  directionLo := (81833978570352595559/25000000000000000000)
  directionHi := (327335914281410382237/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree044.table
  base := (-10576750528546701929916368363301735069751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-17435930558981855416900417933974160000000000000000)
      constant := (218703663716179490297396751561407430934705584833296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree044.table
  base := (-10577489829798369721376195683144740666951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-26160124413190970186919979092929160000000000000000)
      constant := (328214540495629227134685543626518590096675227006744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81833978570352595559/25000000000000000000)
  centralHi := (327335914281410382237/100000000000000000000)
  directionLo := (66224054045245461801/20000000000000000000)
  directionHi := (165560135113113654503/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree045.table
  base := (-10117655369831745361479982360735379956533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-17796240394300786834920476946789915200000000000000)
      constant := (228116726977959543418938848197486076638580481054768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree045.table
  base := (-2529582299360435193327402230090452056363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-8900243574895229915722517629747657600000000000000)
      constant := (114113714894175438155681812072374038535056076628896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66224054045245461801/20000000000000000000)
  centralHi := (165560135113113654503/50000000000000000000)
  directionLo := (66972372193594201587/20000000000000000000)
  directionHi := (5232216577624546999/1562500000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree046.table
  base := (-9619330642611921943090541130591786019261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-54469650688859154758821607878817011200000000000000)
      constant := (713187241298505540291540878285647928917860495274768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree046.table
  base := (-9619944611442939249247382413678901974881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-9080445678726803102471708895185595200000000000000)
      constant := (118922277293643514235640726606465589090410010280888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66972372193594201587/20000000000000000000)
  centralHi := (5232216577624546999/1562500000000000000)
  directionLo := (169281052178895449407/50000000000000000000)
  directionHi := (67712420871558179763/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree047.table
  base := (-1816491967085020420606568222099248583451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-18516860064938649670960594972421425600000000000000)
      constant := (247540569227795107401487243691599176972825858942480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree047.table
  base := (-9083019101862433886456358982195567421807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-27781943347675128867662700481870598400000000000000)
      constant := (371491369967135792233381812215385281282151646270808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169281052178895449407/50000000000000000000)
  centralHi := (67712420871558179763/20000000000000000000)
  directionLo := (342222341590111040797/100000000000000000000)
  directionHi := (171111170795055520399/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree048.table
  base := (-4253824985944231937975168109074478493143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-18877169900257581088980653985237180800000000000000)
      constant := (257551055833927225615481474391142126430407352922656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree048.table
  base := (-4254079634068574816134748084179929631209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-9440849886389949475970091426061470400000000000000)
      constant := (128838184263976350385385038243795439520223566170864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342222341590111040797/100000000000000000000)
  centralHi := (171111170795055520399/50000000000000000000)
  directionLo := (345843842882393375283/100000000000000000000)
  directionHi := (86460960720598343821/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree049.table
  base := (-1973860090616919971367915791733642230357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-57712439206729537521002138994158808000000000000000)
      constant := (803281254190782409351124719904680182472260726336064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree049.table
  base := (-7895904028763000833059028291125800224143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-9621051990221522662719282691499408000000000000000)
      constant := (133945399069020938174780786123554715448527177918664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345843842882393375283/100000000000000000000)
  centralHi := (86460960720598343821/25000000000000000000)
  directionLo := (349427812625017793959/100000000000000000000)
  directionHi := (8735695315625444849/2500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree050.table
  base := (-7246310325013263380092534129083674722613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-19597789570895443925020772010868691200000000000000)
      constant := (278168547321247552156800527940706702612588348774448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree050.table
  base := (-1449346467957341236269486753779534335671/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-29403762282159287548405421870812036800000000000000)
      constant := (417456140442171519731985687196335788607871509392120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349427812625017793959/100000000000000000000)
  centralHi := (8735695315625444849/2500000000000000000)
  directionLo := (176487697030237418397/50000000000000000000)
  directionHi := (70595078812094967359/20000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree051.table
  base := (-3280342999951668503314896287537483357407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-19958099406214375343040831023684446400000000000000)
      constant := (288775347059371121685451877259165655088381743302944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree051.table
  base := (-820133750995565260388642733297298846819/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-9981456197884669036217665222375283200000000000000)
      constant := (144458079263120016132900922844933169449474422245696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176487697030237418397/50000000000000000000)
  centralHi := (70595078812094967359/20000000000000000000)
  directionLo := (356487673543406609309/100000000000000000000)
  directionHi := (35648767354340660931/10000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree052.table
  base := (-116778927393201424346230360322247564403/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-60955227724599920283182670109500604800000000000000)
      constant := (898742194243979560076169774214454670467716326143200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree052.table
  base := (-1167859141693660679410055899302016335607/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-10161658301716242222966856487813220800000000000000)
      constant := (149863453519374030290755868434636765065881766496680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356487673543406609309/100000000000000000000)
  centralHi := (35648767354340660931/10000000000000000000)
  directionLo := (179982842213246395383/50000000000000000000)
  directionHi := (359965684426492790767/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree053.table
  base := (-1016285715809434741087192951957304011677/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42747680000000000000000000000000000000000000000
      center := (277852039)
      previous := (0)
      next := (247944425)
      square := (6432418981691365402530990977779200000000000000)
      linear := (-390164510884004493944923566968225600000000000000)
      constant := (5860087245333668719255762551004849647223057670320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree053.table
  base := (-2540873151577645368248181973051475203829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64121520000000000000000000000000000000000000000
      center := (416887221)
      previous := (0)
      next := (371807475)
      square := (9648628472537048103796486466668800000000000000)
      linear := (-585388324842329174134870627542518400000000000000)
      constant := (8794422533357693788861881623785291574337634939984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179982842213246395383/50000000000000000000)
  centralHi := (359965684426492790767/100000000000000000000)
  directionLo := (363410410611578853781/100000000000000000000)
  directionHi := (181705205305789426891/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree054.table
  base := (-857686527923485876646405133374583065979/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-21039028912171169597101008062131712000000000000000)
      constant := (321786956852016257782503368021018480478495936763920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree054.table
  base := (-1072180385844091235019665360899211263793/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-10522062509379388596465239018689096000000000000000)
      constant := (160972079016717404462521999933813720849215601247456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363410410611578853781/100000000000000000000)
  centralHi := (181705205305789426891/50000000000000000000)
  directionLo := (91705697450158220209/25000000000000000000)
  directionHi := (366822789800632880837/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree055.table
  base := (-1730112796106614302363175478348197085571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-64198016242470303045363201224842401600000000000000)
      constant := (999563008383479909844405964089050433338608689136096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree055.table
  base := (-3460488230828874953110914852193413489303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-10702264613210961783214430284127033600000000000000)
      constant := (166675266077911481285301227319733640454436718622344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91705697450158220209/25000000000000000000)
  centralHi := (366822789800632880837/100000000000000000000)
  directionLo := (18510185823848598263/5000000000000000000)
  directionHi := (370203716476971965261/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree056.table
  base := (-2597045191815482004292288749118682823313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-21759648582809032433141126087763222400000000000000)
      constant := (344786707963704214035745294133682834402631852481648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree056.table
  base := (-1298641950425301883801980974080679154103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-32647400151127604909890864648694913600000000000000)
      constant := (517432997093731826712639993828054553450069974876464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18510185823848598263/5000000000000000000)
  centralHi := (370203716476971965261/100000000000000000000)
  directionLo := (186777022321808360373/50000000000000000000)
  directionHi := (373554044643616720747/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree057.table
  base := (-849551585601839579290413088006087939457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-22119958418127963851161185100578977600000000000000)
      constant := (356584024388897943451107423424150336045949667576544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree057.table
  base := (-169932008461725444826859563893984398857/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-11062668820874108156712812815002908800000000000000)
      constant := (178379253914177213526537329693120633526305717853360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186777022321808360373/50000000000000000000)
  centralHi := (373554044643616720747/100000000000000000000)
  directionLo := (37687459034252779397/10000000000000000000)
  directionHi := (376874590342527793971/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree058.table
  base := (-383294066487125728081604409416418888439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-67440804760340685807543732340184198400000000000000)
      constant := (1105738728019280787834229599416509801447831514925664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree058.table
  base := (-766785199789071355528153049409781566109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-11242870924705681343462004080440846400000000000000)
      constant := (184380009382504001994474091649182685142166495100632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37687459034252779397/10000000000000000000)
  centralHi := (376874590342527793971/100000000000000000000)
  directionLo := (380166133975780506849/100000000000000000000)
  directionHi := (7603322679515610137/2000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree059.table
  base := (200331886569975622058891561874589390021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-22840578088765826687201303126210488000000000000000)
      constant := (380773324745532033212859440165552170431092868376784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree059.table
  base := (200152886883035210868902196421720210181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-34269219085611763590633586037636352000000000000000)
      constant := (571439739260155426026112157774861983182725083534136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380166133975780506849/100000000000000000000)
  centralHi := (7603322679515610137/2000000000000000000)
  directionLo := (23964338902961465971/6250000000000000000)
  directionHi := (383429422447383455537/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree060.table
  base := (1201507143416580717031220496411596261343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-23200887924084758105221362139026243200000000000000)
      constant := (393165236679804893262761457728938065545926160751472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree060.table
  base := (600672293376125315538129248150794020531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-11603275132368827716960386611316721600000000000000)
      constant := (196678948081216478558597656309918046893038534875824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23964338902961465971/6250000000000000000)
  centralHi := (383429422447383455537/100000000000000000000)
  directionLo := (386665171142394196413/100000000000000000000)
  directionHi := (193332585571197098207/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree061.table
  base := (559201042022659472593875121376892621827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-70683593278211068569724263455525995200000000000000)
      constant := (1217265844710121106240951597711691533596225294482496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree061.table
  base := (1118328286319519264119821996738082235917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-11783477236200400903709577876754659200000000000000)
      constant := (202977099262514855416651669381166237991143721439568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386665171142394196413/100000000000000000000)
  centralHi := (193332585571197098207/50000000000000000000)
  directionLo := (9746851643954701371/2500000000000000000)
  directionHi := (389874065758188054841/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree062.table
  base := (1653051987273207206909144204727270991749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-23921507594722620941261480164657753600000000000000)
      constant := (418543432458438200190947736165838273996862830258592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree062.table
  base := (2066231242975525606817341990667727873/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-35891038020095922271376307426577790400000000000000)
      constant := (628123059499409594207118891748438498861863316620800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9746851643954701371/2500000000000000000)
  centralHi := (389874065758188054841/100000000000000000000)
  directionLo := (98264191000289779207/25000000000000000000)
  directionHi := (393056764001159116829/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree063.table
  base := (110232511740673703962822234911912500467/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-24281817430041552359281539177473508800000000000000)
      constant := (431529665308245870358315964923148847666688191310720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree063.table
  base := (4409178861155524766670499203431716880691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-12143881443863547277207960407630534400000000000000)
      constant := (215870697788207799270921251175117730427925899174232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98264191000289779207/25000000000000000000)
  centralHi := (393056764001159116829/100000000000000000000)
  directionLo := (198106948580372770397/50000000000000000000)
  directionHi := (79242779432149108159/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree064.table
  base := (1386574760026839074653155748037206015491/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-73926381796081451331904794570867792000000000000000)
      constant := (1334141876050905946907944701487951524249696482171968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree064.table
  base := (5546188685618459729507574797616332035441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-12324083547695120463957151673068472000000000000000)
      constant := (222466122422164588830164137214173587670255668396232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198106948580372770397/50000000000000000000)
  centralHi := (79242779432149108159/20000000000000000000)
  directionLo := (399346071571448907381/100000000000000000000)
  directionHi := (199673035785724453691/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree065.table
  base := (6717015297050097963170524259341127652407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-25002437100679415195321657203105019200000000000000)
      constant := (458096293465220659077112283467593804889338502028528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree065.table
  base := (3358457586442746147690836109838105386141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-37512856954580080952119028815519228800000000000000)
      constant := (687481852559815293037695573738623355975563207255792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399346071571448907381/100000000000000000000)
  centralHi := (199673035785724453691/50000000000000000000)
  directionLo := (80490773994487527999/20000000000000000000)
  directionHi := (100613467493109409999/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree066.table
  base := (1980343489895304847409622927176622212379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-25362746935998346613341716215920774400000000000000)
      constant := (471676652597163538234094242034485872256092194051264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree066.table
  base := (990160391646854379642870864397509445509/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-12684487755358266837455534203944347200000000000000)
      constant := (235954174563929188353400279639131550683360238785344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80490773994487527999/20000000000000000000)
  centralHi := (100613467493109409999/25000000000000000000)
  directionLo := (405537852773368978139/100000000000000000000)
  directionHi := (20276892638668448907/5000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree067.table
  base := (4579653931144005825446159504249666824483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-77169170313951834094085325686209588800000000000000)
      constant := (1456365062586859303489299731198857535691123771292192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree067.table
  base := (9159225484292203735438199782729158471147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-12864689859189840024204725469382284800000000000000)
      constant := (242846785954975197209628800636332126221433785150744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405537852773368978139/100000000000000000000)
  centralHi := (20276892638668448907/5000000000000000000)
  directionLo := (408598559234216638333/100000000000000000000)
  directionHi := (204299279617108319167/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree068.table
  base := (10430757072277084383262506936599381635831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-26083366606636209449381834241552284800000000000000)
      constant := (499431384682030962799608783456904256468141814647024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree068.table
  base := (10430682369341985893419039341252456330781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-39134675889064239632861750204460667200000000000000)
      constant := (749515334737219188224219038526068878879415492687736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408598559234216638333/100000000000000000000)
  centralHi := (204299279617108319167/50000000000000000000)
  directionLo := (41163650856613847339/10000000000000000000)
  directionHi := (411636508566138473391/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree069.table
  base := (234713362070987302592000081000677614937/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-26443676441955140867401893254368040000000000000000)
      constant := (513605731938464547146237247980386097463619875482400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree069.table
  base := (11735600371704587704233909159442999133263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-13225094066852986397703108000258160000000000000000)
      constant := (256929145385115898092601942814734262208750860811576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41163650856613847339/10000000000000000000)
  centralHi := (411636508566138473391/100000000000000000000)
  directionLo := (414652200959748364719/100000000000000000000)
  directionHi := (5183152511996854559/1250000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree070.table
  base := (51070286006924133360259651229980728941/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-80411958831822216856265856801551385600000000000000)
      constant := (1583934155447584628075993656637114971339274764644352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree070.table
  base := (13073931816363992691688320491306968334983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-13405296170684559584452299265696097600000000000000)
      constant := (264118881972413432295138003054371069620008063137016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414652200959748364719/100000000000000000000)
  centralHi := (5183152511996854559/1250000000000000000)
  directionLo := (417646118546559094643/100000000000000000000)
  directionHi := (104411529636639773661/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree071.table
  base := (902855612611647129183507474162942865197/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 31910240000000000000000000000000000000000000000
      center := (207410677)
      previous := (0)
      next := (185085275)
      square := (4801664873656934737100598898905600000000000000)
      linear := (-382595719895676108499183257464782400000000000000)
      constant := (7641525840277029720728485569347020339495558267648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree071.table
  base := (14445634147923995407074294329979827571613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47865360000000000000000000000000000000000000000
      center := (311197503)
      previous := (0)
      next := (277546425)
      square := (7202497310485402105650898348358400000000000000)
      linear := (-574035138359836595966260163287353600000000000000)
      constant := (11467928867052092181695005086444288023945318202568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417646118546559094643/100000000000000000000)
  centralHi := (104411529636639773661/25000000000000000000)
  directionLo := (210309363149414630659/50000000000000000000)
  directionHi := (420618726298829261319/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree072.table
  base := (15850719813281184372355464910539694345083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-27524605947911935121462070292815305600000000000000)
      constant := (557316571850918740926272595623698356050155513584432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree072.table
  base := (3170133875351492694587245454102250926561/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-13765700378347705957950681796571972800000000000000)
      constant := (278795444725057822575932149715476927056020413952360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210309363149414630659/50000000000000000000)
  centralHi := (420618726298829261319/100000000000000000000)
  directionLo := (423570472872569804153/100000000000000000000)
  directionHi := (211785236436284902077/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree073.table
  base := (4322262321767046684160854512819007930967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-83654747349692599618446387916893182400000000000000)
      constant := (1716848267083096199719581768763036630443247946257216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree073.table
  base := (345780071714171192056893549912860392461/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-13945902482179279144699873062009910400000000000000)
      constant := (286282262744707085880090352641593051872261634363600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423570472872569804153/100000000000000000000)
  centralHi := (211785236436284902077/50000000000000000000)
  directionLo := (426501791398037790529/100000000000000000000)
  directionHi := (42650179139803779053/10000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree074.table
  base := (18760647895217988766609442735110553895199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-28245225618549797957502188318446816000000000000000)
      constant := (587446879318831401782062258230199194229434018058096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree074.table
  base := (9380303245314511560137300734025112489949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-42378313758032556994347192982343544000000000000000)
      constant := (881604301445654137224113612691288492468881054786288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426501791398037790529/100000000000000000000)
  centralHi := (42650179139803779053/10000000000000000000)
  directionLo := (4294131002216610207/1000000000000000000)
  directionHi := (429413100221661020701/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree075.table
  base := (10132744277553924011857793897019404836461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-28605535453868729375522247331262571200000000000000)
      constant := (602808936588404506614106889528016261550438563901088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree075.table
  base := (2533181381098781385442571900703228834269/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-14306306689842425518198255592885785600000000000000)
      constant := (301552954873153844249469402494599954604891010013504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4294131002216610207/1000000000000000000)
  centralHi := (429413100221661020701/100000000000000000000)
  directionLo := (432304803602991719103/100000000000000000000)
  directionHi := (6754762556296745611/1562500000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree076.table
  base := (1362721692505533574785625210781444459827/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-86897535867562982380626919032234979200000000000000)
      constant := (1855106766069876194290444687922878758872522775625984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree076.table
  base := (10901756554942582156074202001797241729391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-14486508793673998704947446858323723200000000000000)
      constant := (309336823182735044259647513029796230345952461233264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432304803602991719103/100000000000000000000)
  centralHi := (6754762556296745611/1562500000000000000)
  directionLo := (435177292369976712613/100000000000000000000)
  directionHi := (217588646184988356307/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree077.table
  base := (1460925116754821490084370403368354469097/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-29326155124506592211562365356894081600000000000000)
      constant := (634126830729267759554718544283234858094785612132608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree077.table
  base := (5843692776232076048479268339049154224577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-44000132692516715675089914371284982400000000000000)
      constant := (951659108901793435255932880532222807720199130257248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435177292369976712613/100000000000000000000)
  centralHi := (217588646184988356307/50000000000000000000)
  directionLo := (438030944535551211583/100000000000000000000)
  directionHi := (6844233508367987681/1562500000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree078.table
  base := (2497923362390805203268036213758787622863/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-29686464959825523629582424369709836800000000000000)
      constant := (650082658334766694915939413396170806275975735015520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree078.table
  base := (1561200360555535652495282433866363160741/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-14846913001337145078445829389199598400000000000000)
      constant := (325201592044373377363683061868455611298747740829312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438030944535551211583/100000000000000000000)
  centralHi := (6844233508367987681/1562500000000000000)
  directionLo := (220433062939155121041/50000000000000000000)
  directionHi := (440866125878310242083/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree079.table
  base := (26616825111740125458136754059701451574547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-90140324385433365142807450147576776000000000000000)
      constant := (1998709202804370291869306021081896205354363277685264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree079.table
  base := (6654199973338653853181503285275061177009/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-15027115105168718265195020654637536000000000000000)
      constant := (333282488464669637862252073532932708188057163344672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220433062939155121041/50000000000000000000)
  centralHi := (440866125878310242083/100000000000000000000)
  directionLo := (221841595244891485169/50000000000000000000)
  directionHi := (443683190489782970339/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree080.table
  base := (14143780467115316357333603841757495229019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-30407084630463386465622542395341347200000000000000)
      constant := (682588055040874363034785174098056668462707287814752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree080.table
  base := (3535942263243161544583489912847121279903/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-45621951627000874355832635760226420800000000000000)
      constant := (1024387171460247420451681412701844721629489174452544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221841595244891485169/50000000000000000000)
  centralHi := (443683190489782970339/100000000000000000000)
  directionLo := (22324124064531400529/5000000000000000000)
  directionHi := (446482481290628010581/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree081.table
  base := (29991427335552006864330023841951308035511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-30767394465782317883642601408157102400000000000000)
      constant := (699137617536462002827787843050797051534862300181744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree081.table
  base := (29991406673542973996505404552306751175663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-15387519312831864638693403185513411200000000000000)
      constant := (349741296554905752235836443172455146391906694136376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22324124064531400529/5000000000000000000)
  centralHi := (446482481290628010581/100000000000000000000)
  directionLo := (112316082629470005201/25000000000000000000)
  directionHi := (89852866103576004161/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree082.table
  base := (31728412025651611308616384994329126141791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-93383112903303747904987981262918572800000000000000)
      constant := (2147655256911256377056067481446981511853923769088592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree082.table
  base := (31728393326751513193851329175349775902033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-15567721416663437825442594450951348800000000000000)
      constant := (358119205279245690346652564062200118087079317788616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112316082629470005201/25000000000000000000)
  centralHi := (89852866103576004161/20000000000000000000)
  directionLo := (452029060185207441377/100000000000000000000)
  directionHi := (226014530092603720689/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree083.table
  base := (33498504023442125504262597906279161835539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-31488014136420180719682719433788612800000000000000)
      constant := (732830456854839895405092555068441815234313319137456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree083.table
  base := (6699697420653588268924862031424160261241/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-47243770561485033036575357149167859200000000000000)
      constant := (1099788346253833359497774825351715341897870805167480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452029060185207441377/100000000000000000000)
  centralHi := (226014530092603720689/50000000000000000000)
  directionLo := (454776982517986326891/100000000000000000000)
  directionHi := (113694245629496581723/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree084.table
  base := (2206355844804076104062662764488543561361/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-31848323971739112137702778446604368000000000000000)
      constant := (749973728966678844531772438566852920100539809282304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree084.table
  base := (8825419552027985877928924611742024437607/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-15928125624326584198940976981827224000000000000000)
      constant := (375172025861413427804192113602218789614036642418656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454776982517986326891/100000000000000000000)
  centralHi := (113694245629496581723/25000000000000000000)
  directionLo := (457508400364854274753/100000000000000000000)
  directionHi := (228754200182427137377/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree085.table
  base := (18568985868998789413292897681888116971697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-96625901421174130667168512378260369600000000000000)
      constant := (2301944699958353679165482261273626188889455782732128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree085.table
  base := (18568978944441726582118251221950043218221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-16108327728158157385690168247265161600000000000000)
      constant := (383846935618168901479945024786664174444437011829584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457508400364854274753/100000000000000000000)
  centralHi := (228754200182427137377/50000000000000000000)
  directionLo := (460223607587280056271/100000000000000000000)
  directionHi := (28763975474205003517/6250000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree086.table
  base := (39007330851569449039263965795030121952199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-32568943642376974973742896472235878400000000000000)
      constant := (784853968137977137591611643082666711990939964186096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree086.table
  base := (9751829581104917283835481387212635019779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-48865589495969191717318078538109297600000000000000)
      constant := (1177862531406656933594688957613002132878277342334496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460223607587280056271/100000000000000000000)
  centralHi := (28763975474205003517/6250000000000000000)
  directionLo := (462922889428567455959/100000000000000000000)
  directionHi := (11573072235714186399/2500000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree087.table
  base := (40909763855444376755512770089279621709629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-32929253477695906391762955485051633600000000000000)
      constant := (802590931835833609901553006333348965056630649076816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree087.table
  base := (10227438131350329375949678462161069422451/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-16468731935821303759188550778141036800000000000000)
      constant := (401493749621804120049590352344584624043764433735008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462922889428567455959/100000000000000000000)
  centralHi := (11573072235714186399/2500000000000000000)
  directionLo := (58200815357950613611/12500000000000000000)
  directionHi := (465606522863604908889/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree088.table
  base := (42845264491767678718977807987445439484793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-99868689939044513429349043493602166400000000000000)
      constant := (2461577368985672495122084996214780550466429206880816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree088.table
  base := (42845254245616623275850023011728837948783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-16648934039652876945937742043578974400000000000000)
      constant := (410465652369345013284414557322284114620227044994616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58200815357950613611/12500000000000000000)
  centralHi := (465606522863604908889/100000000000000000000)
  directionLo := (468274776930574801869/100000000000000000000)
  directionHi := (46827477693057480187/10000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree089.table
  base := (44813827167632170997711134549590315248967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-33649873148333769227803073510683144000000000000000)
      constant := (838658540349004628196390141904565064065018396726768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree089.table
  base := (44813817902732481854532294520270179020877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-50487408430453350398060799927050736000000000000000)
      constant := (1258609654237402248498802461401403478954300948357112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468274776930574801869/100000000000000000000)
  centralHi := (46827477693057480187/10000000000000000000)
  directionLo := (235463956522873443239/50000000000000000000)
  directionHi := (470927913045746886479/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree090.table
  base := (9363089376847043823247817915637541107093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-34010182983652700645823132523498899200000000000000)
      constant := (856989182764632757739551501697134818985670718297360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree090.table
  base := (46815438507547724900961945879242442806929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-17009338247316023319436124574454849600000000000000)
      constant := (428706446185987874945740815383495696656951592088008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235463956522873443239/50000000000000000000)
  centralHi := (470927913045746886479/100000000000000000000)
  directionLo := (118391546325599587351/25000000000000000000)
  directionHi := (94713237060479669881/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree091.table
  base := (24425059586806385529239749937611055567873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-103111478456914896191529574608943963200000000000000)
      constant := (2626553147689503610011856548410092187948509374451552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree091.table
  base := (24425055800407461769919825089033399453237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-17189540351147596506185315839892787200000000000000)
      constant := (437975336184756811977316794914247372626437496272848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118391546325599587351/25000000000000000000)
  centralHi := (94713237060479669881/20000000000000000000)
  directionLo := (47618984075482799021/10000000000000000000)
  directionHi := (476189840754827990211/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree092.table
  base := (25458920021067675678533194571194731807701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-34730802654290563481863250549130409600000000000000)
      constant := (894244138839802472253604085875509114697815093167008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree092.table
  base := (50917833196816423755288520788627688746041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-52109227364937509078803521315992174400000000000000)
      constant := (1342029662871800228171425987629817607617360127382296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47618984075482799021/10000000000000000000)
  centralHi := (476189840754827990211/100000000000000000000)
  directionLo := (478799119688363034311/100000000000000000000)
  directionHi := (59849889961045379289/12500000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree093.table
  base := (13254651480009846926943429765132798784323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-35091112489609494899883309561946164800000000000000)
      constant := (913168450785761276906562249044773794996656526757568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree093.table
  base := (26509299866484322059470614801444703697329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-17549944558810742879683698370768662400000000000000)
      constant := (456810100099943382468008876189865299676145655817616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478799119688363034311/100000000000000000000)
  centralHi := (59849889961045379289/12500000000000000000)
  directionLo := (481394255876193790847/100000000000000000000)
  directionHi := (3760892624032763991/781250000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree094.table
  base := (13788103404086483787126941871290434721039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-106354266974785278953710105724285760000000000000000)
      constant := (2796871953034262397355442623362036324516808978353472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree094.table
  base := (11030481604961461199782457633661510881623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-17730146662642316066432889636206600000000000000000)
      constant := (466375973252046312330792737412941046515164826971480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481394255876193790847/100000000000000000000)
  centralHi := (3760892624032763991/781250000000000000)
  directionLo := (483975476823813140217/100000000000000000000)
  directionHi := (241987738411906570109/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree095.table
  base := (57319260278588938632483332847244765509947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-35811732160247357735923427587577675200000000000000)
      constant := (951610738870518616389747460328558140773779531216688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree095.table
  base := (57319255225776292648833802581527861914527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-53731046299421667759546242704933612800000000000000)
      constant := (1428122520273341420589785550305205742770040781001512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483975476823813140217/100000000000000000000)
  centralHi := (241987738411906570109/50000000000000000000)
  directionLo := (243271502000892122537/50000000000000000000)
  directionHi := (19461720160071369803/4000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree096.table
  base := (14879785839209397824164474298355725427017/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-36172041995566289153943486600393430400000000000000)
      constant := (971128713785335510104569336133930700426506104695872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree096.table
  base := (59519138791305204294943457464136845333431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-18090550870305462439931272167082475200000000000000)
      constant := (485804700328893490919863925043530831752385954478712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243271502000892122537/50000000000000000000)
  centralHi := (19461720160071369803/4000000000000000000)
  directionLo := (244548526533755253891/50000000000000000000)
  directionHi := (489097053067510507783/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree097.table
  base := (61752060571552952509308671392935296325537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-109597055492655661715890636839627556800000000000000)
      constant := (2972533725718238922000383755758728397347664780916144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree097.table
  base := (12350411289343248180175460771613250979867/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-18270752974137035626680463432520412800000000000000)
      constant := (495667553707706787948094004936298836360573292700920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244548526533755253891/50000000000000000000)
  centralHi := (489097053067510507783/100000000000000000000)
  directionLo := (491637834076636274191/100000000000000000000)
  directionHi := (30727364629789767137/6250000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree098.table
  base := (64018009884868540346957108586741033737527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-36892661666204151989983604626024940800000000000000)
      constant := (1010758322771046467540872787023119420151329343393008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree098.table
  base := (64018006158550555923506537708204432061853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-55352865233905826440288964093875051200000000000000)
      constant := (1516888199991602191725557797639599390669076566395768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491637834076636274191/100000000000000000000)
  centralHi := (30727364629789767137/6250000000000000000)
  directionLo := (61770693960583096439/12500000000000000000)
  directionHi := (494165551684664771513/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree099.table
  base := (8289623684366096998286406855797259288151/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-37252971501523083408003663638840696000000000000000)
      constant := (1030869955967471464491109246927004781270900845762432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree099.table
  base := (33158493054474175667073292140781254466229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-18631157181800182000178845963396288000000000000000)
      constant := (515690238991445703134003384466935695384380918923216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 99 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61770693960583096439/12500000000000000000)
  centralHi := (494165551684664771513/100000000000000000000)
  directionLo := (124170101334835240877/25000000000000000000)
  directionHi := (496680405339340963509/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree100.table
  base := (68648997712958525931154524280312471586413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-112839844010526044478071167954969353600000000000000)
      constant := (3153538423379004799193961265772714102582622696822256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree100.table
  base := (68648994672756319579914847489740504118303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-18811359285631755186928037228834225600000000000000)
      constant := (525850070506342141737684008715342670435682931785656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 100 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124170101334835240877/25000000000000000000)
  centralHi := (496680405339340963509/100000000000000000000)
  directionLo := (499182589464311134227/100000000000000000000)
  directionHi := (124795647366077783557/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree101.table
  base := (71014033142772088859361956137271603364501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-37973591172160946244043781664472206400000000000000)
      constant := (1071686877917719503243815712118876982190676844170704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree101.table
  base := (35507015198535554313015874411956179832449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-56974684168389985121031685482816489600000000000000)
      constant := (1608326683131909571027188070848852286797049737146288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 101 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499182589464311134227/100000000000000000000)
  centralHi := (124795647366077783557/25000000000000000000)
  directionLo := (100334458726907564711/20000000000000000000)
  directionHi := (125418073408634455889/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree102.table
  base := (7341209446246127513087322850231553958413/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-38333901007479877662063840677287961600000000000000)
      constant := (1092392166046661335224002795508842376709399528287520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree102.table
  base := (73412091982958759520298110469638701705103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-19171763493294901560426419759710100800000000000000)
      constant := (546466710457183853919321802933651873480678773139256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 102 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100334458726907564711/20000000000000000000)
  centralHi := (125418073408634455889/25000000000000000000)
  directionLo := (126037425685979502131/25000000000000000000)
  directionHi := (20165988109756720341/4000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree103.table
  base := (37921590254015072233736653363348355877419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-116082632528396427240251699070311150400000000000000)
      constant := (3339886015748327083992280284651980835259254047085856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree103.table
  base := (75843178269117957694560185795330668776073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-19351965597126474747175611025148038400000000000000)
      constant := (556923518614430349474803594105154171946017734690696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 103 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126037425685979502131/25000000000000000000)
  centralHi := (20165988109756720341/4000000000000000000)
  directionLo := (101322999433104789837/20000000000000000000)
  directionHi := (253307498582761974593/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree104.table
  base := (39153645119384435304318819596640044801997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-39054520678117740498103958702919472000000000000000)
      constant := (1134396395290276549247132959371565002130043169839776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree104.table
  base := (78307288217279818909170245843814699761467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-58596503102874143801774406871757928000000000000000)
      constant := (1702437956194278522187927831172378459679359177790152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 104 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101322999433104789837/20000000000000000000)
  centralHi := (253307498582761974593/50000000000000000000)
  directionLo := (101813670580971942279/20000000000000000000)
  directionHi := (127267088226214927849/25000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree105.table
  base := (40402211362090709759229259503230495561233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-39414830513436671916124017715735227200000000000000)
      constant := (1155695335958348201440670105802848905369225892108064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree105.table
  base := (16160884179831825369299015402514236116763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-19712369804789621120673993556023913600000000000000)
      constant := (578134110703013923336764899913569604832770712517880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 105 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101813670580971942279/20000000000000000000)
  centralHi := (127267088226214927849/25000000000000000000)
  directionLo := (102301988349300374457/20000000000000000000)
  directionHi := (255754970873250936143/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree106.table
  base := (41667288566150776140297040889065676274321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 128243040000000000000000000000000000000000000000
      center := (833556117)
      previous := (0)
      next := (743833275)
      square := (19297256945074096207592972933337600000000000000)
      linear := (-2251423038608807735894947739351942400000000000000)
      constant := (66633518513122535689760854241151372817014959795168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree106.table
  base := (20833643871197936009159687209561867685143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21373840000000000000000000000000000000000000000
      center := (138962407)
      previous := (0)
      next := (123935825)
      square := (3216209490845682701265495488889600000000000000)
      linear := (-375331545445682911460814807952110400000000000000)
      constant := (11111092347833474296095599856062225532001366743648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 106 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102301988349300374457/20000000000000000000)
  centralHi := (255754970873250936143/50000000000000000000)
  directionLo := (128484982848617538533/25000000000000000000)
  directionHi := (513939931394470154133/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree107.table
  base := (21474438179812338812093275474651203118017/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-40135450184074534752164135741366737600000000000000)
      constant := (1198886868442190891795371583270916454691084650551872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree107.table
  base := (85897751232110590990990511225324485156411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-60218322037358302482517128260699366400000000000000)
      constant := (1799222009531533365277160980174270001651666508643016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 107 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128484982848617538533/25000000000000000000)
  centralHi := (513939931394470154133/100000000000000000000)
  directionLo := (103271697121330515809/20000000000000000000)
  directionHi := (258179242803326289523/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree108.table
  base := (88493948819896289772356100633531225884447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-40495760019393466170184194754182492800000000000000)
      constant := (1220779459938733165045474064448170643604815103864688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree108.table
  base := (44246973738814180727745471766647719495373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-20252976116284340680921567352337726400000000000000)
      constant := (610692436853864136447427596315452432344305222368592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 108 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103271697121330515809/20000000000000000000)
  centralHi := (258179242803326289523/50000000000000000000)
  directionLo := (129691441080897515731/25000000000000000000)
  directionHi := (20750630572943602517/4000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree109.table
  base := (91123164839520847949662598583638976584703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-122568209564137192764612761300994744000000000000000)
      constant := (3728609804260149711935945692971764640534468990150736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree109.table
  base := (3644926545124368819924095030449919594069/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-20433178220115913867670758617775664000000000000000)
      constant := (621743195398030624322238545770752057197685687532200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 109 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129691441080897515731/25000000000000000000)
  centralHi := (20750630572943602517/4000000000000000000)
  directionLo := (521161923791907056497/100000000000000000000)
  directionHi := (260580961895953528249/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree110.table
  base := (2930793757698421337254135773280889932619/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-41216379690031329006224312779814003200000000000000)
      constant := (1265158292765661055873586440445397896989137230136832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree110.table
  base := (93785399153124300066928072903328294829061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-61840140971842461163259849649640804800000000000000)
      constant := (1898678836248768658212214120354420071614271916911416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 110 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521161923791907056497/100000000000000000000)
  centralHi := (260580961895953528249/50000000000000000000)
  directionLo := (523547116682657787631/100000000000000000000)
  directionHi := (32721694792666111727/6250000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree111.table
  base := (12060081820611089299148500931896768769101/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-41576689525350260424244371792629758400000000000000)
      constant := (1287644533867837532188283865166060270799522193672832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree111.table
  base := (96480653578397026993214386354399437508877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-20793582427779060241169141148651539200000000000000)
      constant := (644141686854814230262442741888693508329045098561704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 111 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523547116682657787631/100000000000000000000)
  centralHi := (32721694792666111727/6250000000000000000)
  directionLo := (525921492204841765789/100000000000000000000)
  directionHi := (52592149220484176579/10000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree112.table
  base := (99208927369964343648334288978166811852993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-125810998082007575526793292416336540800000000000000)
      constant := (3930985973890752150107776015826646455969420033719216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree112.table
  base := (12401115809981792079253747384843067586407/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-20973784531610633427918332414089476800000000000000)
      constant := (655489419665665086787817991979838830432124494258112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 112 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (525921492204841765789/100000000000000000000)
  centralHi := (52592149220484176579/10000000000000000000)
  directionLo := (264142598107163693863/50000000000000000000)
  directionHi := (528285196214327387727/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree113.table
  base := (5098510914069633077594430678953954036307/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-42297309195988123260284489818261268800000000000000)
      constant := (1333210664966765160287434265049682668109148561882560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree113.table
  base := (2549255436957719276621378865340288814731/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-63461959906326619844002571038582243200000000000000)
      constant := (2000808431417561763255193255676937460340384623557440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 113 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264142598107163693863/50000000000000000000)
  centralHi := (528285196214327387727/100000000000000000000)
  directionLo := (6632979641480108151/1250000000000000000)
  directionHi := (530638371318408652081/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree114.table
  base := (26191131739804135160840331954232222127199/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-42657619031307054678304548831077024000000000000000)
      constant := (1356290554800359256901289455440850017356267349544384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree114.table
  base := (26191131558676112362901439130613339302777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-21334188739273779801416714944965352000000000000000)
      constant := (678481859236972024569746080703202917861813263658016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 114 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6632979641480108151/1250000000000000000)
  centralHi := (530638371318408652081/100000000000000000000)
  directionLo := (532981156976207075271/100000000000000000000)
  directionHi := (66622644622025884409/12500000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree115.table
  base := (26897963274861609711665727103906214698341/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-129053786599877958288973823531678337600000000000000)
      constant := (4138704982186480941711030880928645996823528175288768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree115.table
  base := (107591852445867032915124751938465509446403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-21514390843105352988165906210403289600000000000000)
      constant := (690126565924675398241925905109050080215457303376856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 115 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532981156976207075271/100000000000000000000)
  centralHi := (66622644622025884409/12500000000000000000)
  directionLo := (267656844797559416811/50000000000000000000)
  directionHi := (535313689595118833623/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree116.table
  base := (110452196430252726595506199914111467565559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-43378238701944917514344666856708534400000000000000)
      constant := (1403043982690581875392740414474053506649061344311536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree116.table
  base := (55226097920352089320379519240024566065939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-65083778840810778524745292427523681600000000000000)
      constant := (2105610791514763004972137508783216099342977346417168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 116 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267656844797559416811/50000000000000000000)
  centralHi := (535313689595118833623/100000000000000000000)
  directionLo := (53763610262349587463/10000000000000000000)
  directionHi := (537636102623495874631/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree117.table
  base := (56672778354280723841159198536638102958927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-43738548537263848932364725869524289600000000000000)
      constant := (1426717520630552448578114537902525843901609804117216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree117.table
  base := (7084097261050541876898103244505188956669/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-21874795050768499361664288741279164800000000000000)
      constant := (713712952950248617585311851606834600916430939783808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 117 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53763610262349587463/10000000000000000000)
  centralHi := (537636102623495874631/100000000000000000000)
  directionLo := (539948526639739186149/100000000000000000000)
  directionHi := (10798970532794783723/2000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree118.table
  base := (116271933717010715760208378020818824675193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-132296575117748341051154354647020134400000000000000)
      constant := (4351766823498477810227520988089951370637540943405616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree118.table
  base := (116271933237421494339281883375467651652263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-22054997154600072548413480006717102400000000000000)
      constant := (725654633236103492003821969326572611211433386499576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 118 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539948526639739186149/100000000000000000000)
  centralHi := (10798970532794783723/2000000000000000000)
  directionLo := (271125544718986266657/50000000000000000000)
  directionHi := (108450217887594506663/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree119.table
  base := (14903915907653687129000029952451298448659/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-44459168207901711768404843895155800000000000000000)
      constant := (1474658244253365112889554228678037330988713505711488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree119.table
  base := (119231326828716681595627216532469776835067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-66705597775294937205488013816465120000000000000000)
      constant := (2213085914021586270945354565769940661757044012311752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 119 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271125544718986266657/50000000000000000000)
  centralHi := (108450217887594506663/20000000000000000000)
  directionLo := (54454391611045572067/10000000000000000000)
  directionHi := (544543916110455720671/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree120.table
  base := (4888949486696183740449616230407771238379/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-44819478043220643186424902907971555200000000000000)
      constant := (1498925429852790388892557958272858175859514370420400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree120.table
  base := (122223736777373776748190886817259717079939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-22415401362263218921911862537592977600000000000000)
      constant := (749834967243890437041743671624678549685952981997528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 120 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54454391611045572067/10000000000000000000)
  centralHi := (544543916110455720671/100000000000000000000)
  directionLo := (109365425825377553323/20000000000000000000)
  directionHi := (68353391140860970827/12500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree121.table
  base := (12524916328010527220744102999979758644203/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-135539363635618723813334885762361931200000000000000)
      constant := (4570171493787660872801473756135704733560940168147360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree121.table
  base := (125249162928407442755027612106102268843351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-22595603466094792108661053803030915200000000000000)
      constant := (762073620928631583663411176161669443364842277490552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 121 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109365425825377553323/20000000000000000000)
  centralHi := (68353391140860970827/12500000000000000000)
  directionLo := (549100848410742247649/100000000000000000000)
  directionHi := (10982016968214844953/2000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree122.table
  base := (128307605460338229958578964726827071754249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-45540097713858506022465020933603065600000000000000)
      constant := (1548053448451164120411074395561693832517044676929296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree122.table
  base := (64153802571613465976572560588781606745061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-68327416709779095886230735205406558400000000000000)
      constant := (2323233797137157348730498292054314425868876976414832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 122 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (549100848410742247649/100000000000000000000)
  centralHi := (10982016968214844953/2000000000000000000)
  directionLo := (137841297853192360823/25000000000000000000)
  directionHi := (551365191412769443293/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree123.table
  base := (131399063583808482717968523832974643294547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-45900407549177437440485079946418820800000000000000)
      constant := (1572914281390461269645053417539441421298248036775088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree123.table
  base := (65699531648950528905160721821394362038249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-22956007673757938482159436333906790400000000000000)
      constant := (786847901581113942416674138824231318213740644865296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 123 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137841297853192360823/25000000000000000000)
  centralHi := (551365191412769443293/100000000000000000000)
  directionLo := (553620273181792753741/100000000000000000000)
  directionHi := (276810136590896376871/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree124.table
  base := (8407721096210272423281011333960602334653/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-138782152153489106575515416877703728000000000000000)
      constant := (4793918990165786746014955015823910231731569435922176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree124.table
  base := (134523537281606885890128371800493019005601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-23136209777589511668908627599344728000000000000000)
      constant := (799383528522261890337369355160710506659516176852552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 124 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553620273181792753741/100000000000000000000)
  centralHi := (276810136590896376871/50000000000000000000)
  directionLo := (111173241286584027857/20000000000000000000)
  directionHi := (277933103216460069643/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree125.table
  base := (137681027227607090540096547627883263755681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-46621027219815300276525197972050331200000000000000)
      constant := (1623229594423047003933208882187864261782832282721424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree125.table
  base := (137681026995242674442754065756492173695141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-69949235644263254566973456594347996800000000000000)
      constant := (2436054439573809742143834646176165046140813224931896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 125 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111173241286584027857/20000000000000000000)
  centralHi := (277933103216460069643/50000000000000000000)
  directionLo := (22324124064531400529/4000000000000000000)
  directionHi := (279051550806642506613/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree126.table
  base := (7043576627982378432605199003024801168553/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-46981337055134231694545256984866086400000000000000)
      constant := (1648684074473676578455008427413875336436194548946240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree126.table
  base := (3521788308754691520570874355546097209129/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-23496613985252658042407010130220603200000000000000)
      constant := (824751755578098933740662839896732118006942394496320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 126 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22324124064531400529/4000000000000000000)
  centralHi := (279051550806642506613/50000000000000000000)
  directionLo := (560331066965425081119/100000000000000000000)
  directionHi := (3502069168533906757/625000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree127.table
  base := (144095053455994671208215169530735313641881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (44178474201)
      previous := (0)
      next := (39423163575)
      square := (1022754618088927099002427565466892800000000000000)
      linear := (-142024940671359489337695947993045524800000000000000)
      constant := (5023009310567423746145971914461360380950977941018672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree127.table
  base := (144095053267193136140949776274026770790483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-23676816089084231229156201395658540800000000000000)
      constant := (837584355673771548528275162943012703979340022973016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 127 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560331066965425081119/100000000000000000000)
  centralHi := (3502069168533906757/625000000000000000)
  directionLo := (281275104294201016531/50000000000000000000)
  directionHi := (562550208588402033063/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree128.table
  base := (147351589845561233826868655360019896441629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-47701956725772094530585375010497596800000000000000)
      constant := (1700186681553335314532176462134069593231615444404816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree128.table
  base := (7367579483769545029043870095874856636549/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (22095022713)
      previous := (0)
      next := (19705796175)
      square := (511377309044463549501213782733446400000000000000)
      linear := (-71571054578747413247716177983289435200000000000000)
      constant := (2551547840410779138765382530572744850955666600054880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 128 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell134.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281275104294201016531/50000000000000000000)
  centralHi := (562550208588402033063/100000000000000000000)
  directionLo := (564760630496759738871/100000000000000000000)
  directionHi := (70595078812094967359/12500000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 95449
  qDenominator := 180624
  table := BinomialMassData.Q95449_180624.Degree129.table
  base := (37660285416193800831050498573439953192039/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14726158067)
      previous := (0)
      next := (13141054525)
      square := (340918206029642366334142521822297600000000000000)
      linear := (-48062266561091025948605434023313352000000000000000)
      constant := (1726234808551855719637398215046917273657287148453824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95449_180624.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 47737
  qDenominator := 90312
  table := BinomialMassData.Q47737_90312.Degree129.table
  base := (30128228302281333311835898535392461277857/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7365007571)
      previous := (0)
      next := (6568598725)
      square := (170459103014821183167071260911148800000000000000)
      linear := (-24037220296747377602654583926534416000000000000000)
      constant := (863546528960384301941731171583697045020816443113320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47737_90312.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 129 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage99KernelData.Cell134.Kernel129
