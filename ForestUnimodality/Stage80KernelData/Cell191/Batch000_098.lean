import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell191.Parameters
import ForestUnimodality.BinomialMassData.Q2587_4752.Batch000_049
import ForestUnimodality.BinomialMassData.Q2587_4752.Batch050_099
import ForestUnimodality.BinomialMassData.Q6_11.Batch000_049
import ForestUnimodality.BinomialMassData.Q6_11.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree000.table
  base := (302308478404511630677120591/10000000000000000000000000)
  polynomial :=
    { denominator := 11880000000000000000000000000000000000000000
      center := (43979)
      previous := (0)
      next := (36805)
      square := (1948099496291516795620779579600000000000000)
      linear := (-6959546959148630076441577291200000000000000)
      constant := (359142472344559817244419262108000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree000.table
  base := (302308478404511630677120591/10000000000000000000000000)
  polynomial :=
    { denominator := 27500000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (85)
      square := (4509489574748881471344397175000000000000)
      linear := (-16110062405436643695466614100000000000000)
      constant := (831348315612406984362081625250000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree001.table
  base := (95231356725552358613214506943686121947413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-2696952121480412376487018052039550000000000000)
      constant := (68498851383406030103924147690741980859374826536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree001.table
  base := (47560274356481603261294799621622101377747/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1122)
      previous := (0)
      next := (935)
      square := (49604385322237696184788368925000000000000)
      linear := (-231324561356789658306265521200000000000000)
      constant := (5866211901084253832513870284116274266707387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9958591954639383881/20000000000000000000)
  directionHi := (24896479886598459703/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree002.table
  base := (122149607357795159746235673534513449369891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-3326918796093681620270887648592700000000000000)
      constant := (46035233044468509119732875637790218671874860876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree002.table
  base := (121874814217022888809422745304365674447547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-1141753745015104943849593149200000000000000)
      constant := (15756268787998488054912947183428246608153187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9958591954639383881/20000000000000000000)
  centralHi := (24896479886598459703/50000000000000000000)
  directionLo := (2816715160878121371/4000000000000000000)
  directionHi := (17604469755488258569/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree003.table
  base := (3189904676455423369177955769942946799789/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-439653941189661207117195249460650000000000000)
      constant := (3672993827594443790428056244717589970973198900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree003.table
  base := (39742854226299006021225337035316404494671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-679104622301525627237062106800000000000000)
      constant := (5654497539290378464644261104273284943855191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2816715160878121371/4000000000000000000)
  centralHi := (17604469755488258569/25000000000000000000)
  directionLo := (43121968093205172709/50000000000000000000)
  directionHi := (86243936186410345419/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree004.table
  base := (6609972991289418471973451522578207363587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-4586852145320220107838626841699000000000000000)
      constant := (25902621178101354087919469940546159986708661856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree004.table
  base := (52650625189729053722813415384674687053509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-1574664744190997565098655278000000000000000)
      constant := (8861824727990171741586808314345637133474589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43121968093205172709/50000000000000000000)
  centralHi := (86243936186410345419/100000000000000000000)
  directionLo := (9958591954639383881/10000000000000000000)
  directionHi := (99585919546393838811/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree005.table
  base := (4426673429344082408382517165459928207989/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-5216818819933489351622496438252150000000000000)
      constant := (22408418494082659190955483716747449146052054432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree005.table
  base := (8804427092573770373248070032314647100527/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1122)
      previous := (0)
      next := (935)
      square := (49604385322237696184788368925000000000000)
      linear := (-447780060944735968930796585600000000000000)
      constant := (1917595788298524919137011029410072299163767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9958591954639383881/10000000000000000000)
  centralHi := (99585919546393838811/100000000000000000000)
  directionLo := (22268088570756164529/20000000000000000000)
  directionHi := (55670221426890411323/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree006.table
  base := (5926911506777583077677233178718617047677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-649642832727417621711818448311700000000000000)
      constant := (2365526405677204102772901824359369900948516432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree006.table
  base := (11769767957202465108241137487306820077499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-1003787871683445093173858703400000000000000)
      constant := (3646666141262854876327562712764125229377379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22268088570756164529/20000000000000000000)
  centralHi := (55670221426890411323/50000000000000000000)
  directionLo := (121967344227261256167/100000000000000000000)
  directionHi := (15245918028407657021/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree007.table
  base := (15588251706714379464007796876582092551441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-6476752169160027839190235631358450000000000000)
      constant := (21779404511412080256579626023446202019980236676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree007.table
  base := (3088109714138872663412124950498449091673/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-2224031242954836496972248471200000000000000)
      constant := (7467429446569929344185096442651561700462165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121967344227261256167/100000000000000000000)
  centralHi := (15245918028407657021/12500000000000000000)
  directionLo := (131739788601722168851/100000000000000000000)
  directionHi := (32934947150430542213/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree008.table
  base := (9747003655377569445774542611034588225491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-7106718843773297082974105227911600000000000000)
      constant := (23415838731148479249498814327271499971129342476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree008.table
  base := (9613341573514880226596077116624066812117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-2440486742542782807596779535600000000000000)
      constant := (8034478668683289882394075635111512084266157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131739788601722168851/100000000000000000000)
  centralHi := (32934947150430542213/25000000000000000000)
  directionLo := (140835758043906068551/100000000000000000000)
  directionHi := (17604469755488258569/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree009.table
  base := (5389408563877181958506317552310631679987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (483769)
      previous := (0)
      next := (404855)
      square := (21429094459206684751828575375600000000000000)
      linear := (-286543908088391345435480549054250000000000000)
      constant := (959952387742634302400887589382518772294070116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree009.table
  base := (2632389018141479781777214325108557546943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-1328471121065364559110655300000000000000000)
      constant := (4449255192794592640058212194738135463180103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140835758043906068551/100000000000000000000)
  centralHi := (17604469755488258569/12500000000000000000)
  directionLo := (29875775863918151643/20000000000000000000)
  directionHi := (18672359914948844777/12500000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree010.table
  base := (506826907285088456320266681455658662819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-8366652192999835570541844421017900000000000000)
      constant := (29115791725679004250662607592602136369817618736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree010.table
  base := (1908015439413349690035621153368049855821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-2873397741718675428845841664400000000000000)
      constant := (10000616652417800089166235663557534032554341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29875775863918151643/20000000000000000000)
  centralHi := (18672359914948844777/12500000000000000000)
  directionLo := (1968239554055542379/1250000000000000000)
  directionHi := (157459164324443390321/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree011.table
  base := (-643543589193071784703093412110334022093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1187433)
      previous := (0)
      next := (993735)
      square := (52598686399870953481761048649200000000000000)
      linear := (-817874442510282255847792183415550000000000000)
      constant := (2990883828152108837405629907552334863407344932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree011.table
  base := (-760110801130706028079040707467485024363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (408)
      previous := (0)
      next := (340)
      square := (18037958298995525885377588700000000000000)
      linear := (-280895749209692885406397520800000000000000)
      constant := (1027646777681880614255922483817857664732007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1968239554055542379/1250000000000000000)
  centralHi := (157459164324443390321/100000000000000000000)
  directionLo := (165144564768954090841/100000000000000000000)
  directionHi := (82572282384477045421/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree012.table
  base := (-352004427063603453842552834261647628819/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-1069620615802930450901064846013800000000000000)
      constant := (4133605218909544960373731069945375930878239392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree012.table
  base := (-1465836579954110147608757664072137374607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-1653154370447284025047451896600000000000000)
      constant := (6392881661208102372913688199447271377672553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165144564768954090841/100000000000000000000)
  centralHi := (82572282384477045421/50000000000000000000)
  directionLo := (43121968093205172709/25000000000000000000)
  directionHi := (172487872372820690837/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree013.table
  base := (-576866270473674714043524899904737626241/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-10256552216839643301893453210677350000000000000)
      constant := (41979945672459310821913881182408516271761044192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree013.table
  base := (-4730841642877722285484749983202195163807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-3522764240482514360719434857600000000000000)
      constant := (14430538385443372026136224274032534385179353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43121968093205172709/25000000000000000000)
  centralHi := (172487872372820690837/100000000000000000000)
  directionLo := (89765534809688631897/50000000000000000000)
  directionHi := (35906213923875452759/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree014.table
  base := (-1530694439203436526579901842517526482889/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-10886518891452912545677322807230500000000000000)
      constant := (47203091630881269178113433636983275353533507184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree014.table
  base := (-6239748423853953000196895753308371809947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-3739219740070460671343965922000000000000000)
      constant := (16228501750550604936582436666649687010996413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89765534809688631897/50000000000000000000)
  centralHi := (35906213923875452759/20000000000000000000)
  directionLo := (46577048936179992651/25000000000000000000)
  directionHi := (37261639148943994121/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree015.table
  base := (-1848894316107540071054102347265201261237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-1279609507340686865495688044864850000000000000)
      constant := (5872458484221736150405141229417955511517858608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree015.table
  base := (-7514102393059791452234102513843748683393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-3955675239658406981968496986400000000000000)
      constant := (18172912642020935116607515441824906409309447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46577048936179992651/25000000000000000000)
  centralHi := (37261639148943994121/20000000000000000000)
  directionLo := (96423651979983753327/50000000000000000000)
  directionHi := (38569460791993501331/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree016.table
  base := (-8472335037204799092071995468077190825733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-12146452240679451033245062000336800000000000000)
      constant := (58913287009094018125913356196949116297811671212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree016.table
  base := (-8592709860566240927332790472938157020207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-4172130739246353292593028050800000000000000)
      constant := (20259075496335771168637353754374483000554953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96423651979983753327/50000000000000000000)
  centralHi := (38569460791993501331/20000000000000000000)
  directionLo := (9958591954639383881/5000000000000000000)
  directionHi := (199171839092787677621/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree017.table
  base := (-9380968009589941190178799266607878823303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-12776418915292720277028931596889950000000000000)
      constant := (65376723484692043301531747910866500280001062692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree017.table
  base := (-9503350145626710706993000076256037217847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-4388586238834299603217559115200000000000000)
      constant := (22483629015865450569610446710373019496640513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9958591954639383881/5000000000000000000)
  centralHi := (199171839092787677621/100000000000000000000)
  directionLo := (102650816278511044771/50000000000000000000)
  directionHi := (205301632557022089543/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree018.table
  base := (-2535500454059660049818596426398058867483/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (483769)
      previous := (0)
      next := (404855)
      square := (21429094459206684751828575375600000000000000)
      linear := (-496532799626147760030103747905300000000000000)
      constant := (2675377540813379853821292101854414416878928624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree018.table
  base := (-1283306756154992588779828382861907050221/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1122)
      previous := (0)
      next := (935)
      square := (49604385322237696184788368925000000000000)
      linear := (-1151260434605561478460522544900000000000000)
      constant := (6211025268422281447331225731347418493846518) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102650816278511044771/50000000000000000000)
  centralHi := (205301632557022089543/100000000000000000000)
  directionLo := (211253637065859102827/100000000000000000000)
  directionHi := (52813409266464775707/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree019.table
  base := (-10770925892252898212163626260895676056181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-14036352264519258764596670789996250000000000000)
      constant := (79483232130578006370425873082498733555541320684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree019.table
  base := (-5448722701800879216825623328681121916099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-2410748619005096112233310622000000000000000)
      constant := (13669312693055550850347175898629584248152021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211253637065859102827/100000000000000000000)
  centralHi := (52813409266464775707/25000000000000000000)
  directionLo := (217042479751151308163/100000000000000000000)
  directionHi := (54260619937787827041/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree020.table
  base := (-563986063640560983446743247703955306067/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-14666318939132528008380540386549400000000000000)
      constant := (87116611730014051460661695956963669512570879760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree020.table
  base := (-5704129839597622678691483971870701008173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-2518976368799069267545576154200000000000000)
      constant := (14982878880601462722310194063403645178011067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217042479751151308163/100000000000000000000)
  centralHi := (54260619937787827041/25000000000000000000)
  directionLo := (22268088570756164529/10000000000000000000)
  directionHi := (222680885707561645291/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree021.table
  base := (-5838935896923245564998401544544662610071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-1699587290416199694684934442566950000000000000)
      constant := (10570220684614908373494887871131624906569553032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree021.table
  base := (-590417450242133313932899016815425171301/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1122)
      previous := (0)
      next := (935)
      square := (49604385322237696184788368925000000000000)
      linear := (-1313602059296521211428920843200000000000000)
      constant := (8181088622844275745159721248726667771362895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22268088570756164529/10000000000000000000)
  centralHi := (222680885707561645291/100000000000000000000)
  directionLo := (228180007236566058539/100000000000000000000)
  directionHi := (11409000361828302927/5000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree022.table
  base := (-2993261888714721994275442228840128780503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1187433)
      previous := (0)
      next := (993735)
      square := (52598686399870953481761048649200000000000000)
      linear := (-1447841117123551499631661779968700000000000000)
      constant := (9411513557991921290164253931085839866946343088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree022.table
  base := (-12105361484328060676345198658426031874179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (408)
      previous := (0)
      next := (340)
      square := (18037958298995525885377588700000000000000)
      linear := (-497351248797639196030928585200000000000000)
      constant := (3237590014188705957436973064357313649384031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228180007236566058539/100000000000000000000)
  centralHi := (11409000361828302927/5000000000000000000)
  directionLo := (116774841624228445637/50000000000000000000)
  directionHi := (9341987329938275651/4000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree023.table
  base := (-12171576700186947417412767572559637914299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-16556218962972335739732149176208850000000000000)
      constant := (112298367862009095837693537080782980409370398036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree023.table
  base := (-2461122037060493327341406667576468530401/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-5687319236361977466964745501600000000000000)
      constant := (38632400874113137489686092604116236539107395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116774841624228445637/50000000000000000000)
  centralHi := (9341987329938275651/4000000000000000000)
  directionLo := (59699661529834987031/25000000000000000000)
  directionHi := (382077833790943917/160000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree024.table
  base := (-12278777773794236486635491537260624834959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-1909576181953956109279557641418000000000000000)
      constant := (13493918417783347906722663182892934463970267364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree024.table
  base := (-1241440359486368848195434284585426041441/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-2951887367974961888794638283000000000000000)
      constant := (20890222159275192265644768904225817244928195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59699661529834987031/25000000000000000000)
  centralHi := (382077833790943917/160000000000000000)
  directionLo := (48786937690904502467/20000000000000000000)
  directionHi := (15245918028407657021/6250000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree025.table
  base := (-3074799581601773370639941014343677607587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-17816152312198874227299888369315150000000000000)
      constant := (130965738292426161860599117862204519483097733072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree025.table
  base := (-12436282914998735951933856180665395078867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-6120230235537870088213807630400000000000000)
      constant := (45057071003947078478095585112139487195457093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48786937690904502467/20000000000000000000)
  centralHi := (15245918028407657021/6250000000000000000)
  directionLo := (9958591954639383881/4000000000000000000)
  directionHi := (124482399432992298513/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree026.table
  base := (-12236789160288024110714625579095747183253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-18446118986812143471083757965868300000000000000)
      constant := (140858391473870094474862940214414054196849744492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree026.table
  base := (-1237519538317951139783679889548085134397/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-3168342867562908199419169347400000000000000)
      constant := (24230901657284559572805048111623408493689815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9958591954639383881/4000000000000000000)
  centralHi := (124482399432992298513/50000000000000000000)
  directionLo := (126947636761535828817/50000000000000000000)
  directionHi := (50779054704614331527/20000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree027.table
  base := (-12095033481549549640515254119898550216389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (483769)
      previous := (0)
      next := (404855)
      square := (21429094459206684751828575375600000000000000)
      linear := (-706521691163904174624726946756350000000000000)
      constant := (5597110974217407831432594887099676683272228548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree027.table
  base := (-489384910332832637394225315903373078831/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-6553141234713762709462869759200000000000000)
      constant := (51994219957587815598894783250992296436536225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126947636761535828817/50000000000000000000)
  centralHi := (50779054704614331527/20000000000000000000)
  directionLo := (129365904279615518127/50000000000000000000)
  directionHi := (51746361711846207251/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree028.table
  base := (-2375408771324789372164007548322787128783/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-19706052336038681958651497158974600000000000000)
      constant := (161755454556936213968976844863852030403143607060) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree028.table
  base := (-2403535556993402776706698268306736343419/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-6769596734301709020087400823600000000000000)
      constant := (55653944290913299755163927083674424512231505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129365904279615518127/50000000000000000000)
  centralHi := (51746361711846207251/20000000000000000000)
  directionLo := (263479577203444337703/100000000000000000000)
  directionHi := (32934947150430542213/12500000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree029.table
  base := (-1448204473173460642938094351896844974457/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-20336019010651951202435366755527750000000000000)
      constant := (172757772823354288088458126813609868765239919584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree029.table
  base := (-5863588697045051722452205013272419912023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-3493026116944827665355965944000000000000000)
      constant := (29720317732948979916046204694794037190645217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263479577203444337703/100000000000000000000)
  centralHi := (32934947150430542213/12500000000000000000)
  directionLo := (134071647306842053039/50000000000000000000)
  directionHi := (268143294613684106079/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree030.table
  base := (-701461502288782074155349869695267878097/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-2329553965029468938468804039120100000000000000)
      constant := (20458671403556340266171772230859248739713363392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree030.table
  base := (-11365698750993426543581351613430174395253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-7202507733477601641336462952400000000000000)
      constant := (63353981645540091456802061686774948898174387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134071647306842053039/50000000000000000000)
  centralHi := (268143294613684106079/100000000000000000000)
  directionLo := (34090909090909090909/12500000000000000000)
  directionHi := (272727272727272727273/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree031.table
  base := (-5396333057367368708553880790169561414231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-21595952359878489690003105948634050000000000000)
      constant := (195865425113747716339641545595903073070196781768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree031.table
  base := (-5467811248046655966412175436185302038409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-3709481616532773975980497008400000000000000)
      constant := (33696847386174659425074209884021578453352511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34090909090909090909/12500000000000000000)
  centralHi := (272727272727272727273/100000000000000000000)
  directionLo := (277235466945034658851/100000000000000000000)
  directionHi := (69308866736258664713/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree032.table
  base := (-10295696018196925460109032424100429433827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-22225919034491758933786975545187200000000000000)
      constant := (207969139090213300066302931690635700880286216628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree032.table
  base := (-10439166323459074582396503678098709906913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-7635418732653494262585525081200000000000000)
      constant := (71559506505343254900790149032550056101263527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277235466945034658851/100000000000000000000)
  centralHi := (69308866736258664713/25000000000000000000)
  directionLo := (281671516087812137103/100000000000000000000)
  directionHi := (17604469755488258569/6250000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree033.table
  base := (-4867275305519825111771722384350216575691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (131937)
      previous := (0)
      next := (110415)
      square := (5844298488874550386862338738800000000000000)
      linear := (-230867532415202304823947930724650000000000000)
      constant := (2226651027969757744251959142502937593748474552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree033.table
  base := (-1234801400976645218751301950873777915831/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27500000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (85)
      square := (4509489574748881471344397175000000000000)
      linear := (-178451687096396376663864912400000000000000)
      constant := (1723890114695010988421455095580776885851718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281671516087812137103/100000000000000000000)
  centralHi := (17604469755488258569/6250000000000000000)
  directionLo := (143019388386838847317/50000000000000000000)
  directionHi := (57207755354735538927/20000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree034.table
  base := (-9111190334905842324542460802128864781493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-23485852383718297421354714738293500000000000000)
      constant := (233272671435738341116338419254806891115957135852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree034.table
  base := (-9255321999846973206489569924034407181121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-8068329731829386883834587210000000000000000)
      constant := (80268432649127345247140403811991836731084359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143019388386838847317/50000000000000000000)
  centralHi := (57207755354735538927/20000000000000000000)
  directionLo := (290340353139478399983/100000000000000000000)
  directionHi := (18146272071217399999/6250000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree035.table
  base := (-8427475561043389422151931370330813553341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-24115819058331566665138584334846650000000000000)
      constant := (246471141684460653682419222302604027381593374924) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree035.table
  base := (-8571763683709253627784548090481460184847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-8284785231417333194459118274400000000000000)
      constant := (84811083649901842064789267495051743317633513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290340353139478399983/100000000000000000000)
  centralHi := (18146272071217399999/6250000000000000000)
  directionLo := (294579122654902737771/100000000000000000000)
  directionHi := (73644780663725684443/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree036.table
  base := (-7685179568324070895250411061819938216317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (483769)
      previous := (0)
      next := (404855)
      square := (21429094459206684751828575375600000000000000)
      linear := (-916510582701660589219350145607400000000000000)
      constant := (9630860623649961156676310020903312047389169444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree036.table
  base := (-978689284816577778183627198622289356731/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1122)
      previous := (0)
      next := (935)
      square := (49604385322237696184788368925000000000000)
      linear := (-2125310182751319876270912334700000000000000)
      constant := (22369725727147231754722550372333405975671098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294579122654902737771/100000000000000000000)
  centralHi := (73644780663725684443/25000000000000000000)
  directionLo := (298757758639181516431/100000000000000000000)
  directionHi := (18672359914948844777/6250000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree037.table
  base := (-688599890085746068155250843386778597241/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-25375752407558105152706323527952950000000000000)
      constant := (273958358296165788129974392415249621181138745240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree037.table
  base := (-3515137567145469115100669361658480450417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-4358848115296612907854090201600000000000000)
      constant := (47135842280920881571266772099039323865499543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298757758639181516431/100000000000000000000)
  centralHi := (18672359914948844777/6250000000000000000)
  directionLo := (302878749981048760647/100000000000000000000)
  directionHi := (37859843747631095081/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree038.table
  base := (-1507890421074690045195236077703609585169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-26005719082171374396490193124506100000000000000)
      constant := (288245931595967485740488721930407758083629242864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree038.table
  base := (-1543919799618111261805038761684841436729/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1122)
      previous := (0)
      next := (935)
      square := (49604385322237696184788368925000000000000)
      linear := (-2233537932545293031583177866900000000000000)
      constant := (24797307755753568245921354937836134186155791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302878749981048760647/100000000000000000000)
  centralHi := (37859843747631095081/12500000000000000000)
  directionLo := (306944418475166039693/100000000000000000000)
  directionHi := (153472209237583019847/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree039.table
  base := (-640429293477157930253628880609445771209/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-2959520639642738182252673635673250000000000000)
      constant := (33655044893927963002966385683639718616384178912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree039.table
  base := (-5267297698413304658779637816736064203979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-9150607229769118436957242532000000000000000)
      constant := (104231352173598780942493073426974936231318541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306944418475166039693/100000000000000000000)
  centralHi := (153472209237583019847/50000000000000000000)
  directionLo := (155478467058973360791/50000000000000000000)
  directionHi := (310956934117946721583/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree040.table
  base := (-832625419577056168395160403708569173629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-27265652431397912884057932317612400000000000000)
      constant := (317906242789107467884534716659753916435267190780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree040.table
  base := (-2153322791853511497751456936793338548727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-4683531364678532373790886798200000000000000)
      constant := (54698932352347236400675553438648006035604033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155478467058973360791/50000000000000000000)
  centralHi := (310956934117946721583/100000000000000000000)
  directionLo := (314918328648886780641/100000000000000000000)
  directionHi := (157459164324443390321/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree041.table
  base := (-788024603172636993974139668197260860093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-27895619106011182127841801914165550000000000000)
      constant := (333277933223625040437505902192170037881172905008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree041.table
  base := (-131807439841902266626825298881214196191/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-9583518228945011058206304660800000000000000)
      constant := (114688591576156379810657561542484327056522225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314918328648886780641/100000000000000000000)
  centralHi := (157459164324443390321/50000000000000000000)
  directionLo := (318830507577276034851/100000000000000000000)
  directionHi := (79707626894319008713/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree042.table
  base := (-104587938317136677877130378443555923931/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-3169509531180494596847296834524300000000000000)
      constant := (38778886409206825068369541305350907921164181520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree042.table
  base := (-2234333974473955100504110737049241491909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-9799973728532957368830835725200000000000000)
      constant := (120103361568260776989234658050417041779479011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318830507577276034851/100000000000000000000)
  centralHi := (79707626894319008713/25000000000000000000)
  directionLo := (32269526089634269323/10000000000000000000)
  directionHi := (322695260896342693231/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree043.table
  base := (-983473745913085565420304470534118199467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-29155552455237720615409541107271850000000000000)
      constant := (365101894338536752566250356785461569183472861588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree043.table
  base := (-1125459558052725470240188001428213985387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-10016429228120903679455366789600000000000000)
      constant := (125642008906280616969483738841827186107768173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32269526089634269323/10000000000000000000)
  centralHi := (322695260896342693231/100000000000000000000)
  directionLo := (326514272655781288279/100000000000000000000)
  directionHi := (8162856816394532207/2500000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree044.table
  base := (171433311438307157797830540352785903873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1187433)
      previous := (0)
      next := (993735)
      square := (52598686399870953481761048649200000000000000)
      linear := (-2707774466350089987199400973075000000000000000)
      constant := (34686656024514618562126014182588530960652630348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree044.table
  base := (7527396895962957319008173902053037229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27500000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (85)
      square := (4509489574748881471344397175000000000000)
      linear := (-232565561993382954319997678500000000000000)
      constant := (2984190294151690768716080601112922583409519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (326514272655781288279/100000000000000000000)
  centralHi := (8162856816394532207/2500000000000000000)
  directionLo := (165144564768954090841/50000000000000000000)
  directionHi := (330289129537908181683/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree045.table
  base := (1371679061809605505688140089536166595383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (483769)
      previous := (0)
      next := (404855)
      square := (21429094459206684751828575375600000000000000)
      linear := (-1126499474239417003813973344458450000000000000)
      constant := (14754203358011282635695524883107144562568465044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree045.table
  base := (153885740137746871687724135332911957721/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1122)
      previous := (0)
      next := (935)
      square := (49604385322237696184788368925000000000000)
      linear := (-2612335056824199075176107229600000000000000)
      constant := (34272574471235179382634101780250564693768482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165144564768954090841/50000000000000000000)
  centralHi := (330289129537908181683/100000000000000000000)
  directionLo := (66804265712268493587/20000000000000000000)
  directionHi := (10438166517541952123/3125000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree046.table
  base := (327002275074750732014182402875986285699/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-31045452479077528346761149896931300000000000000)
      constant := (415532278140173398688609015558006343226807138912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree046.table
  base := (2476220076531571667315241594215833914843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-10665795726884742611328959982800000000000000)
      constant := (142999632559797209342860576818500115903696003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66804265712268493587/20000000000000000000)
  centralHi := (10438166517541952123/3125000000000000000)
  directionLo := (168856142009151908827/50000000000000000000)
  directionHi := (67542456803660763531/20000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree047.table
  base := (3903241750336510256453884933968835821511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-31675419153690797590545019493484450000000000000)
      constant := (433059152120493561068265091053507185968418655196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree047.table
  base := (470537394264390407468877882974459276957/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1122)
      previous := (0)
      next := (935)
      square := (49604385322237696184788368925000000000000)
      linear := (-2720562806618172230488372761800000000000000)
      constant := (37258057551593302375928311891579819145023594) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168856142009151908827/50000000000000000000)
  centralHi := (67542456803660763531/20000000000000000000)
  directionLo := (170681666868350795603/50000000000000000000)
  directionHi := (341363333736701591207/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree048.table
  base := (5232175542602689858034165419046555417419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-3589487314256007426036543232226400000000000000)
      constant := (50104855368708402466388468576122301158584494476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree048.table
  base := (5094145203613336043769072549147170590581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-11098706726060635232578022111600000000000000)
      constant := (155187948292689763474542571506446807641460301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170681666868350795603/50000000000000000000)
  centralHi := (341363333736701591207/100000000000000000000)
  directionLo := (43121968093205172709/12500000000000000000)
  directionHi := (344975744745641381673/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree049.table
  base := (3300839428281323075308490208514470716239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-32935352502917336078112758686590750000000000000)
      constant := (469185514246443432661544298821101881391769807608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree049.table
  base := (3232306931479257222097504400781365137529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-5657581112824290771601276588000000000000000)
      constant := (80733324175468340045376224253894545181641009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43121968093205172709/12500000000000000000)
  centralHi := (344975744745641381673/100000000000000000000)
  directionLo := (87137679603094608959/25000000000000000000)
  directionHi := (348550718412378435837/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree050.table
  base := (4005321592375698125456927951733001416017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-33565319177530605321896628283143900000000000000)
      constant := (487784208783357077759801363940619861825243548424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree050.table
  base := (7874593123126287171136494915564124279399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-11531617725236527853827084240400000000000000)
      constant := (167868195828022010426265905804783259037807279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87137679603094608959/25000000000000000000)
  centralHi := (348550718412378435837/100000000000000000000)
  directionLo := (352089395109765171379/100000000000000000000)
  directionHi := (17604469755488258569/5000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree051.table
  base := (472899555148733381757938776413505396241/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-3799476205793763840631166431077450000000000000)
      constant := (56304377975008171905785767377639459123584643280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree051.table
  base := (9323002196331535610209905605469187876477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-11748073224824474164451615304800000000000000)
      constant := (174392459948623755128742524737861771733053717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352089395109765171379/100000000000000000000)
  centralHi := (17604469755488258569/5000000000000000000)
  directionLo := (71118571693119804159/20000000000000000000)
  directionHi := (88898214616399755199/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree052.table
  base := (10942675226131576637595980595969438005917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-34825252526757143809464367476250200000000000000)
      constant := (526050723666423385449265327320432197628255730612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree052.table
  base := (5404395234764240569374708397784388637843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-5982264362206210237538073184600000000000000)
      constant := (90519656794281687492419870296931911025179003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71118571693119804159/20000000000000000000)
  centralHi := (88898214616399755199/25000000000000000000)
  directionLo := (359062139238754527589/100000000000000000000)
  directionHi := (35906213923875452759/10000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree053.table
  base := (12463677235602776833704962392764895897541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-35455219201370413053248237072803350000000000000)
      constant := (545717815157938216936339508493109040121404776276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree053.table
  base := (2466187305801303788520412296885534087743/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-12180984224000366785700677433600000000000000)
      constant := (187808633156781886812045044365615748123084515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359062139238754527589/100000000000000000000)
  centralHi := (35906213923875452759/10000000000000000000)
  directionLo := (181249109430698962547/50000000000000000000)
  directionHi := (72499643772279585019/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree054.table
  base := (876250435428640208590076543178479300413/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (483769)
      previous := (0)
      next := (404855)
      square := (21429094459206684751828575375600000000000000)
      linear := (-1336488365777173418408596543309500000000000000)
      constant := (20953345440145404657503779779472345629964753344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree054.table
  base := (13888447244855286469273729834728127649477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-12397439723588313096325208498000000000000000)
      constant := (194700298484560136741506648762802103445586717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181249109430698962547/50000000000000000000)
  centralHi := (72499643772279585019/20000000000000000000)
  directionLo := (365902032681783768503/100000000000000000000)
  directionHi := (45737754085222971063/12500000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree055.table
  base := (3902675387073848340580085241985319595591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1187433)
      previous := (0)
      next := (993735)
      square := (52598686399870953481761048649200000000000000)
      linear := (-3337741140963359230983270569628150000000000000)
      constant := (53283447191692885727090994987449332882892707664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree055.table
  base := (3870089226601542497921512257194214217691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 27500000000000000000000000000000000000000
      center := (102)
      previous := (0)
      next := (85)
      square := (4509489574748881471344397175000000000000)
      linear := (-286679436890369531976130444600000000000000)
      constant := (4584413470929709602551092515329136356394601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (365902032681783768503/100000000000000000000)
  centralHi := (45737754085222971063/12500000000000000000)
  directionLo := (184637236468999099101/50000000000000000000)
  directionHi := (369274472937998198203/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree056.table
  base := (86174122920821118794491950774528960063/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-37345119225210220784599845862462800000000000000)
      constant := (606850261437894820561298985607334440030557733600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree056.table
  base := (8552863200792335955254057286420588316941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-6415175361382102858787135313400000000000000)
      constant := (104425101116631064957375135328456891186349861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184637236468999099101/50000000000000000000)
  centralHi := (369274472937998198203/100000000000000000000)
  directionLo := (46577048936179992651/12500000000000000000)
  directionHi := (372616391489439941209/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree057.table
  base := (18891465375882885071932644012995332070857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-4219453988869276669820412828779550000000000000)
      constant := (69770781393833370334234017002342189311005877828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree057.table
  base := (9381821217269707749516972863345621419331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-6523403111176076014099400845600000000000000)
      constant := (108054108256413421182540912520264820191739051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46577048936179992651/12500000000000000000)
  centralHi := (372616391489439941209/100000000000000000000)
  directionLo := (23495537645608332559/6250000000000000000)
  directionHi := (75185720465946664189/20000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree058.table
  base := (10289869088590797161802793400802723593157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-38605052574436759272167585055569100000000000000)
      constant := (649377919905267435191661226119326540813430286504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree058.table
  base := (4090643355407092477643123226249389116879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-13263261721940098338823332755600000000000000)
      constant := (223488128083984932320587934735880880415711795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23495537645608332559/6250000000000000000)
  centralHi := (75185720465946664189/20000000000000000000)
  directionLo := (37921188390207654919/10000000000000000000)
  directionHi := (379211883902076549191/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree059.table
  base := (22298781479403007834504288822307905407911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-39235019249050028515951454652122250000000000000)
      constant := (671172619548927504597494864439000327425005685596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree059.table
  base := (2217358554997956934633097726528931454017/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-6739858610764022324723931910000000000000000)
      constant := (115494916208683058675115109885950003529680285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37921188390207654919/10000000000000000000)
  centralHi := (379211883902076549191/100000000000000000000)
  directionLo := (382466981235684174037/100000000000000000000)
  directionHi := (191233490617842087019/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree060.table
  base := (24047757323986288356331789609520700393119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-4429442880407033084415036027630600000000000000)
      constant := (77035648423725974406029662404140774538211837276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree060.table
  base := (1495244283258485391903119843519053237483/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1122)
      previous := (0)
      next := (935)
      square := (49604385322237696184788368925000000000000)
      linear := (-3424043180278997740018098721100000000000000)
      constant := (59653306961550211267888534160263221766941772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (382466981235684174037/100000000000000000000)
  centralHi := (191233490617842087019/50000000000000000000)
  directionLo := (385694607919935013309/100000000000000000000)
  directionHi := (38569460791993501331/10000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree061.table
  base := (12912925319855836556243634496720549771481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-40494952598276567003519193845228550000000000000)
      constant := (715822281112617334142932790728693954110840540232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree061.table
  base := (12851684246816211688934403971957615465409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-6956314110351968635348462974400000000000000)
      constant := (123179107742837324140426273124406871471314489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (385694607919935013309/100000000000000000000)
  centralHi := (38569460791993501331/10000000000000000000)
  directionLo := (38889544793104431927/10000000000000000000)
  directionHi := (388895447931044319271/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree062.table
  base := (13816134301357443190540324945207838147017/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-41124919272889836247303063441781700000000000000)
      constant := (738676675709377222474883544475393336810881780424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree062.table
  base := (1719448159518063488138443697961794404389/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1122)
      previous := (0)
      next := (935)
      square := (49604385322237696184788368925000000000000)
      linear := (-3532270930072970895330364253300000000000000)
      constant := (63556174788760920867565592528213508491724276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38889544793104431927/10000000000000000000)
  centralHi := (388895447931044319271/100000000000000000000)
  directionLo := (49008769665563237897/12500000000000000000)
  directionHi := (392070157324505903177/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree063.table
  base := (14733120008810832283458610660853588474057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (483769)
      previous := (0)
      next := (404855)
      square := (21429094459206684751828575375600000000000000)
      linear := (-1546477257314929833003219742160550000000000000)
      constant := (28217916574011939295564633401276717825857953752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree063.table
  base := (29346541551127277056290220263301022655099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-14345539219879829891945988077600000000000000)
      constant := (262212585302313580391928581153859423741266979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49008769665563237897/12500000000000000000)
  centralHi := (392070157324505903177/100000000000000000000)
  directionLo := (79043873161033301311/20000000000000000000)
  directionHi := (98804841451291626639/25000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree064.table
  base := (7831753679605464496220968422902910891113/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-42384852622116374734870802634888000000000000000)
      constant := (785443231793878392484720893668618285868706985872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree064.table
  base := (15604364727848525114841520382337165509541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-7280997359733888101285259571000000000000000)
      constant := (135160891465657935031297716292662797026654461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79043873161033301311/20000000000000000000)
  centralHi := (98804841451291626639/25000000000000000000)
  directionLo := (398343678185575355241/100000000000000000000)
  directionHi := (199171839092787677621/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree065.table
  base := (4151732873489449508815960228055903750547/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-43014819296729643978654672231441150000000000000)
      constant := (809354871125547383457831607670547170658324010336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree065.table
  base := (33097002770057293270310407974937609900239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-14778450219055722513195050206400000000000000)
      constant := (278552203531041686392992862930967450797928919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398343678185575355241/100000000000000000000)
  centralHi := (199171839092787677621/50000000000000000000)
  directionLo := (200721837871087428517/50000000000000000000)
  directionHi := (80288735148434971407/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree066.table
  base := (17563037497366509562887082139218670555601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (131937)
      previous := (0)
      next := (110415)
      square := (5844298488874550386862338738800000000000000)
      linear := (-440856423952958719418571129575700000000000000)
      constant := (8420388030699677960435832687942094433720323928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree066.table
  base := (7002129994083881455725523520494957948767/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (408)
      previous := (0)
      next := (340)
      square := (18037958298995525885377588700000000000000)
      linear := (-1363173247149424438529052842800000000000000)
      constant := (26082160091555691719661451179227222687182185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200721837871087428517/50000000000000000000)
  centralHi := (80288735148434971407/20000000000000000000)
  directionLo := (404519917477945251747/100000000000000000000)
  directionHi := (101129979369486312937/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree067.table
  base := (37062960247063609061907668629606984938241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-44274752645956182466222411424547450000000000000)
      constant := (858233619904672140400318303037113180450169201476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree067.table
  base := (7389795791118549610510021428988163037209/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-15211361218231615134444112335200000000000000)
      constant := (295376371615284569683992500644137838637511445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404519917477945251747/100000000000000000000)
  centralHi := (101129979369486312937/25000000000000000000)
  directionLo := (407572941299270802039/100000000000000000000)
  directionHi := (10189323532481770051/2500000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree068.table
  base := (3902384706233864139972626948511835112967/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-44904719320569451710006281021100600000000000000)
      constant := (883200248727968631939000517915177343539188244120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree068.table
  base := (2431957282092388062974438634770118092769/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1122)
      previous := (0)
      next := (935)
      square := (49604385322237696184788368925000000000000)
      linear := (-3856954179454890361267160849900000000000000)
      constant := (75992488474223394199854891519228737156900196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (407572941299270802039/100000000000000000000)
  centralHi := (10189323532481770051/2500000000000000000)
  directionLo := (82120653022808835817/20000000000000000000)
  directionHi := (205301632557022089543/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree069.table
  base := (2050404102609827908962062737729264034243/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-5059409555020302328198905624183750000000000000)
      constant := (100946452330024628226091500391259594156469251440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree069.table
  base := (204485039014704421595168979712053368631/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1122)
      previous := (0)
      next := (935)
      square := (49604385322237696184788368925000000000000)
      linear := (-3911068054351876938923293616000000000000000)
      constant := (78171107154040576664441614037957922880217550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82120653022808835817/20000000000000000000)
  centralHi := (205301632557022089543/50000000000000000000)
  directionLo := (413611387857357302959/100000000000000000000)
  directionHi := (5170142348216966287/1250000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree070.table
  base := (10753757405532671537303737167761815059663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-46164652669795990197574020214206900000000000000)
      constant := (934186862370807850124513563288678912363565017072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree070.table
  base := (42905415850461535473335307555572768531811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-15860727716995454066317705528400000000000000)
      constant := (321519718699294931398894451782224304992349131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (413611387857357302959/100000000000000000000)
  centralHi := (5170142348216966287/1250000000000000000)
  directionLo := (416597790450530909689/100000000000000000000)
  directionHi := (41659779045053090969/10000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree071.table
  base := (22522035742637632488292831488652629142053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-46794619344409259441357889810760050000000000000)
      constant := (960206404775862652795194543379287960924430824616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree071.table
  base := (4493592106102241309098354677126907750263/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-8038591608291700188471118296400000000000000)
      constant := (165237874587647151673941300107461779188909115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (416597790450530909689/100000000000000000000)
  centralHi := (41659779045053090969/10000000000000000000)
  directionLo := (419562936698702772131/100000000000000000000)
  directionHi := (104890734174675693033/25000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree072.table
  base := (23547303094915999521959921720810769141223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (483769)
      previous := (0)
      next := (404855)
      square := (21429094459206684751828575375600000000000000)
      linear := (-1756466148852686247597842941011600000000000000)
      constant := (36539869850797754022755320676009410262275004328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree072.table
  base := (46987920742728682936554165955775559244981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-16293638716171346687566767657200000000000000)
      constant := (339552447118441147562244555386248842668642701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419562936698702772131/100000000000000000000)
  centralHi := (104890734174675693033/25000000000000000000)
  directionLo := (84501454826343641131/20000000000000000000)
  directionHi := (52813409266464775707/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree073.table
  base := (4916604865967748983464686297560807836097/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-48054552693635797928925629003866350000000000000)
      constant := (1013296899521918892143118194128218784749071210920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree073.table
  base := (12265207161176106291028273706419807172347/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1122)
      previous := (0)
      next := (935)
      square := (49604385322237696184788368925000000000000)
      linear := (-4127523553939823249547824680400000000000000)
      constant := (87187435398094869435155573697976796667853987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84501454826343641131/20000000000000000000)
  centralHi := (52813409266464775707/12500000000000000000)
  directionLo := (13294726087269988959/3125000000000000000)
  directionHi := (425431234792639646689/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree074.table
  base := (25628914873861827752133327714840883238121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-48684519368249067172709498600419500000000000000)
      constant := (1040367444611419282935682125667227777006411322312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree074.table
  base := (25577037253916802572297785634145221117747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-8363274857673619654407914893000000000000000)
      constant := (179033781797878126846449491108131571755247387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13294726087269988959/3125000000000000000)
  centralHi := (425431234792639646689/100000000000000000000)
  directionLo := (85667047195561792459/20000000000000000000)
  directionHi := (53541904497226120287/12500000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree075.table
  base := (13342348950407485073888020396384680943621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-5479387338095815157388152021885850000000000000)
      constant := (118643102876840366517880939775116842939354870736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree075.table
  base := (66583879534928590462160454498815451201/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1122)
      previous := (0)
      next := (935)
      square := (49604385322237696184788368925000000000000)
      linear := (-4235751303733796404860090212600000000000000)
      constant := (91876461502341625001893389156371333919064200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85667047195561792459/20000000000000000000)
  centralHi := (53541904497226120287/12500000000000000000)
  directionLo := (43121968093205172709/10000000000000000000)
  directionHi := (431219680932051727091/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree076.table
  base := (5550020824148880881620757787129953674477/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-49944452717475605660277237793525800000000000000)
      constant := (1095558153331970684161181193586242568346877667720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree076.table
  base := (55399376431045564111107353987827832019077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-17159460714523131930064891914800000000000000)
      constant := (377064523544757830494509119762127167674308317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43121968093205172709/10000000000000000000)
  centralHi := (431219680932051727091/100000000000000000000)
  directionLo := (217042479751151308163/50000000000000000000)
  directionHi := (434084959502302616327/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree077.table
  base := (57649743149125531456753559594191210259707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1187433)
      previous := (0)
      next := (993735)
      square := (52598686399870953481761048649200000000000000)
      linear := (-4597674490189897718551009762734450000000000000)
      constant := (102152540188677121867268181250285588197790361732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree077.table
  base := (28775184030142840947577941301630603773579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 55000000000000000000000000000000000000000
      center := (204)
      previous := (0)
      next := (170)
      square := (9018979149497762942688794350000000000000)
      linear := (-789814373368685374576791953600000000000000)
      constant := (17579251486102303151745586172117936641509369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217042479751151308163/50000000000000000000)
  centralHi := (434084959502302616327/100000000000000000000)
  directionLo := (218465724376325741449/50000000000000000000)
  directionHi := (436931448752651482899/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree078.table
  base := (2392699634746809687621067930653581713143/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-5689376229633571571982775220736900000000000000)
      constant := (128016345810784196416427897367377856687051454300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree078.table
  base := (59719567974237505413835200772919584512713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-17592371713699024551313954043600000000000000)
      constant := (396542811682332504381982196109523269726038273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218465724376325741449/50000000000000000000)
  centralHi := (436931448752651482899/100000000000000000000)
  directionLo := (87951902708711450753/20000000000000000000)
  directionHi := (219879756771778626883/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree079.table
  base := (62002955618075194361182547968110305267983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-51834352741315413391628846583185250000000000000)
      constant := (1180965489067044367045646492325520225482034049788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree079.table
  base := (6190647955623140720880296594943591950287/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-8904413606643485430969242554000000000000000)
      constant := (203231150209193155351393798641340873129923635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87951902708711450753/20000000000000000000)
  centralHi := (219879756771778626883/50000000000000000000)
  directionLo := (55321188384718568527/12500000000000000000)
  directionHi := (442569507077748548217/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree080.table
  base := (64205655111263450667430184869849342233449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-52464319415928682635412716179738400000000000000)
      constant := (1210132902217517896183697957410140162516281211364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree080.table
  base := (16027654933597430545599762747155115461759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1122)
      previous := (0)
      next := (935)
      square := (49604385322237696184788368925000000000000)
      linear := (-4506320678218729293140754043100000000000000)
      constant := (104125485112678722706000555980405768970872839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55321188384718568527/12500000000000000000)
  centralHi := (442569507077748548217/100000000000000000000)
  directionLo := (445361771415123290581/100000000000000000000)
  directionHi := (222680885707561645291/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree081.table
  base := (33212560095303616029102794259608606686907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (483769)
      previous := (0)
      next := (404855)
      square := (21429094459206684751828575375600000000000000)
      linear := (-1966455040390442662192466139862650000000000000)
      constant := (45912932822695466670842379512590328981869001352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree081.table
  base := (33165759306034257370444421353883231651909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-9120869106231431741593773618400000000000000)
      constant := (213330837460912164269392093915619871029880989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (445361771415123290581/100000000000000000000)
  centralHi := (222680885707561645291/50000000000000000000)
  directionLo := (224068318979386137323/50000000000000000000)
  directionHi := (448136637958772274647/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree082.table
  base := (68660894469445061645495992385609972999193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-53724252765155221122980455372844700000000000000)
      constant := (1269514180023179389973526488123324211683143261348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree082.table
  base := (34284359554206006825741934156464851090247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-9229096856025404896906039150600000000000000)
      constant := (218470724262465537763983041901732246981919887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224068318979386137323/50000000000000000000)
  centralHi := (448136637958772274647/100000000000000000000)
  directionLo := (56361803489260201911/12500000000000000000)
  directionHi := (450894427914081615289/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree083.table
  base := (70912533984356866836041763401924195376129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-54354219439768490366764324969397850000000000000)
      constant := (1299727727002445981032529325367431645712231851844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree083.table
  base := (35410888304368269850255099625417580919199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-9337324605819378052218304682800000000000000)
      constant := (223670603730829203303346683241675527291223079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56361803489260201911/12500000000000000000)
  centralHi := (450894427914081615289/100000000000000000000)
  directionLo := (28352215795169656697/6250000000000000000)
  directionHi := (453635452722714507153/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree084.table
  base := (73179606856925497636262663460569949600003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-6109354012709084401172021618439000000000000000)
      constant := (147809963863147131083846431297703509304118517612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree084.table
  base := (36545129312235041527996848774254658844233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-9445552355613351207530570215000000000000000)
      constant := (228930449700444554292648582588084813720152193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28352215795169656697/6250000000000000000)
  centralHi := (453635452722714507153/100000000000000000000)
  directionLo := (456360014473132117079/100000000000000000000)
  directionHi := (11409000361828302927/2500000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree085.table
  base := (75461692964721801470484548191181557504147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-55614152788995028854332064162504150000000000000)
      constant := (1361199875086496573661601594655961681336033210892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree085.table
  base := (37686872231191206770969282072509179226951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-9553780105407324362842835747200000000000000)
      constant := (234250236719371161806240994097773610686461071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (456360014473132117079/100000000000000000000)
  centralHi := (11409000361828302927/2500000000000000000)
  directionLo := (114767101572296340379/25000000000000000000)
  directionHi := (459068406289185361517/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree086.table
  base := (38879191810629279896991645478773544061313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-56244119463608298098115933759057300000000000000)
      constant := (1392458183757657758511034182351507465634834867336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree086.table
  base := (77671824902848820920318264762029892236773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-19324015710402595036310202558800000000000000)
      constant := (479259880059643461749446624893805616960649533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114767101572296340379/25000000000000000000)
  centralHi := (459068406289185361517/100000000000000000000)
  directionLo := (461760912698192514081/100000000000000000000)
  directionHi := (230880456349096257041/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree087.table
  base := (40034640632333157288998465053785143269247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-6319342904246840815766644817290050000000000000)
      constant := (158229384500851995801097709918276655825955118776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree087.table
  base := (79984101886898357598905261843676474509421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-19540471209990541346934733623200000000000000)
      constant := (490139071098457038337531543226684853415639941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (461760912698192514081/100000000000000000000)
  centralHi := (230880456349096257041/50000000000000000000)
  directionLo := (232218904989905470447/50000000000000000000)
  directionHi := (92887561995962188179/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree088.table
  base := (8239399915485145331258157446158958226609/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1187433)
      previous := (0)
      next := (993735)
      square := (52598686399870953481761048649200000000000000)
      linear := (-5227641164803166962334879359287600000000000000)
      constant := (132365324443699955899507150236967447440767102840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree088.table
  base := (82310188211804851709745110755348572440287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 110000000000000000000000000000000000000000
      center := (408)
      previous := (0)
      next := (340)
      square := (18037958298995525885377588700000000000000)
      linear := (-1796084246325317059778114971600000000000000)
      constant := (45557999973059380598246750490308834296843157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232218904989905470447/50000000000000000000)
  centralHi := (92887561995962188179/20000000000000000000)
  directionLo := (467099366496913782549/100000000000000000000)
  directionHi := (9341987329938275651/2000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree089.table
  base := (16946432215780785475143148723356819480643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-58134019487448105829467542548716750000000000000)
      constant := (1488320376135294086649532401318553816603860767740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree089.table
  base := (16929941446997204237906684214600419573257/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-19973382209166433968183795752000000000000000)
      constant := (512256620301479450349334930152633253841820485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467099366496913782549/100000000000000000000)
  centralHi := (9341987329938275651/2000000000000000000)
  directionLo := (469745843009593208289/100000000000000000000)
  directionHi := (46974584300959320829/10000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree090.table
  base := (8708340106452868885479429810070465360469/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (483769)
      previous := (0)
      next := (404855)
      square := (21429094459206684751828575375600000000000000)
      linear := (-2176443931928199076787089338713700000000000000)
      constant := (56332213079379665998127729200345352163306088920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree090.table
  base := (17400458517196557405833950808797532279271/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-20189837708754380278808326816400000000000000)
      constant := (523494888561110281083292414415322507028958955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469745843009593208289/100000000000000000000)
  centralHi := (46974584300959320829/10000000000000000000)
  directionLo := (236188746486665085481/50000000000000000000)
  directionHi := (472377492973330170963/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree091.table
  base := (2236184077532034403884030534797411268113/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-59393952836674644317035281741823050000000000000)
      constant := (1553966574291269054026786030833589971400336738720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree091.table
  base := (17873517577259477332913111707912524667949/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-20406293208342326589432857880800000000000000)
      constant := (534852761360747449512331993494887077424109145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236188746486665085481/50000000000000000000)
  centralHi := (472377492973330170963/100000000000000000000)
  directionLo := (474994562822295684489/100000000000000000000)
  directionHi := (47499456282229568449/10000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree092.table
  base := (91823700869394984133258319564423499493793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-60023919511287913560819151338376200000000000000)
      constant := (1587310717385266991854500228079298654867391946948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree092.table
  base := (91745246476875151263362722783292651763121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-20622748707930272900057388945200000000000000)
      constant := (546330196754645340707738335866378410863337641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474994562822295684489/100000000000000000000)
  centralHi := (47499456282229568449/10000000000000000000)
  directionLo := (477597292238679896249/100000000000000000000)
  directionHi := (382077833790943917/80000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree093.table
  base := (94212077475990240593492043576970810254743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-6739320687322353644955891214992150000000000000)
      constant := (180111340395256538283155392919656571457726944572) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree093.table
  base := (23533732788255213410482700183000713469887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1122)
      previous := (0)
      next := (935)
      square := (49604385322237696184788368925000000000000)
      linear := (-5209801051879554802670480002400000000000000)
      constant := (139481788485258958045073039389643086329856327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (477597292238679896249/100000000000000000000)
  centralHi := (382077833790943917/80000000000000000)
  directionLo := (480185914408882067611/100000000000000000000)
  directionHi := (120046478602220516903/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree094.table
  base := (96612165198468194751815213085223016860913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-61283852860514452048386890531482500000000000000)
      constant := (1655040497175063688709570317302454579627137099268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree094.table
  base := (48268156953273186704276003797014576136167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 605000000000000000000000000000000000000000
      center := (2244)
      previous := (0)
      next := (1870)
      square := (99208770644475392369576737850000000000000)
      linear := (-10527829853553082760653225537000000000000000)
      constant := (284821796615464080681297803305838763712476207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (480185914408882067611/100000000000000000000)
  centralHi := (120046478602220516903/25000000000000000000)
  directionLo := (48276065626733649709/10000000000000000000)
  directionHi := (482760656267336497091/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree095.table
  base := (4951182261744455937151907667304263593087/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-61913819535127721292170760128035650000000000000)
      constant := (1689425905753730318516973507078280350795108894640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree095.table
  base := (98949075674952076569397366903803376417863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-21272115206694111831930982138400000000000000)
      constant := (581479476017759872541395376873360208546561423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48276065626733649709/10000000000000000000)
  centralHi := (482760656267336497091/100000000000000000000)
  directionLo := (485321738728695964127/100000000000000000000)
  directionHi := (15166304335271748879/3125000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree096.table
  base := (50723103730573621160476387853248396101811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1451307)
      previous := (0)
      next := (1214565)
      square := (64287283377620054255485726126800000000000000)
      linear := (-6949309578860110059550514413843200000000000000)
      constant := (191573131096706638935557447604043900241550796888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree096.table
  base := (101372906097449779948589947753336894837617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-21488570706282058142555513202800000000000000)
      constant := (593434764747875595552410359703753764275351657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (485321738728695964127/100000000000000000000)
  centralHi := (15166304335271748879/3125000000000000000)
  directionLo := (487869376909045024671/100000000000000000000)
  directionHi := (15245918028407657021/3125000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree097.table
  base := (51939775097378046791004566421029499138013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-63173752884354259779738499321141950000000000000)
      constant := (1759237213080510187618139932162647336528219909736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree097.table
  base := (5190375163882023815630958602790750592933/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 302500000000000000000000000000000000000000
      center := (1122)
      previous := (0)
      next := (935)
      square := (49604385322237696184788368925000000000000)
      linear := (-5426256551467501113295011066800000000000000)
      constant := (151377355722952762630096443788588404108724465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell191.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487869376909045024671/100000000000000000000)
  centralHi := (15245918028407657021/3125000000000000000)
  directionLo := (245201890168385040389/50000000000000000000)
  directionHi := (490403780336770080779/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 2587
  qDenominator := 4752
  table := BinomialMassData.Q2587_4752.Degree098.table
  base := (106323379965064313494948294117887246955983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (13061763)
      previous := (0)
      next := (10931085)
      square := (578585550398580488299371535141200000000000000)
      linear := (-63803719558967529023522368917695100000000000000)
      constant := (1794662901837170887196188942207546895916961217788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q2587_4752.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 6
  qDenominator := 11
  table := BinomialMassData.Q6_11.Degree098.table
  base := (106252573552665142616946484138390765324247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (4488)
      previous := (0)
      next := (3740)
      square := (198417541288950784739153475700000000000000)
      linear := (-21921481705457950763804575331600000000000000)
      constant := (617703414916360295656932457988745282604233887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q6_11.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell191.Kernel098
