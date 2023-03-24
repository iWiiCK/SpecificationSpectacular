/*
@author Heshan Wickramaratne
*/

//Main Class
class Main {
  static method main() {
    
    var carPark := new CarPark(5, 10, false);
  }
}

// CarPark Class
class {:autocontracts} CarPark{
  const totalFreeSpaces: int;
  const reservedSpaces: int;
  const normalSpaces: int;
  const isWeekEnd: bool;
  const parkingMargin: int;
  var carsInNormalSpaces: int;
  var carsInReservedSpaces: int;

  //Constructor for setting the car park for a new day.
  constructor(totalFreeSpaces: int, reservedSpaces: int, isWeekEnd: bool)
  {          
    this.totalFreeSpaces := totalFreeSpaces;
    this.reservedSpaces := reservedSpaces;
    this.isWeekEnd := isWeekEnd;
    parkingMargin := 5;
    carsInNormalSpaces := 0;
    carsInReservedSpaces := 0;

    if isWeekEnd {
      normalSpaces := totalFreeSpaces;
    }
    else{
      normalSpaces := totalFreeSpaces - reservedSpaces;
    }
  }

  //To allow any car without registration to enter the car park.
  method enterCarPark(){}

  // to allow any car from any area to leave the car park.
  method leaveCarPark(){}

  //to report on the number of non-reserved free spaces currently available.
  method checkAvailability(){}

  // to allow a car with a subscription to enter the car park's reservered area on a weekday,
  // or to enter the carpark generally on a weekend day.
  method enterReservedCarPark(){}

  // to allow a car to be registered as a having a reserved space when the owner pays the subscription,
  // AS LONG AS SUBSCRIPTIONS ARE AVAIALBLE
  method makeSubscription(){}

  // to remove parking restrictions on the reserved spaces
  // AT THE WEEKEND
  method openReservedArea(){}

  //to remove and crush remaining cars at closing time.
  method closeCarPark(){}


  //to display car parks in rows, indicating the state of each space.
  method printParkingPlan(){}

  method canSubscriptionCarEnter() returns (result: bool){
    return carsInReservedSpaces < (reservedSpaces - parkingMargin);
  }

  method canNormalCarEnter() returns (result: bool){
    return carsInNormalSpaces < (normalSpaces - parkingMargin);
  }

  //State invarients of the class
  /////////////////////////////////
  predicate valid(){
    carsInNormalSpaces > 0
  }
}
