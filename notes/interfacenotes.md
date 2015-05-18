# Things to do

* ~~Move index attribute into attrs for Objects~~
* ~~Move shape attribute into attrs for Objects~~
* ~~Have MouseDown events also update WorkingVal~~
  - ~~Write util function to update a val given an ID~~
  - ~~Make sure given IDs are unique~~
  - ~~Have SelectObject send the correct ID over its event handler~~
  - ~~Call util function to perform updates in MouseDown code~~

## Zones

* Create children SVGs along with the parent Objects
  - ~~Create center SVG~~
  - Create border SVGs
* Tie event handlers only to the children SVGs
  - ~~Center SVG~~
  - Border SVGs
* ~~SelectObject takes an ID and a zone keyword~~
* MovingObj keeps track of what type of zone is selected
* MouseDown code only changes attributes that are manipulable by that zone
  - ~~Util function to propagate attribute changes to children SVGs along with
  parent needed~~ (Obseleted by change of approach)
* MouseDown gives an outline to the proper zone

## Syncing

* ~~Have Model track inputExp~~
* ~~Create function to generate static/not manipulatable text box and image~~
  - Still need to make visuals non-manipulatable
* ~~Have Model track if we're in a manipulable state or not~~
* ~~Hook Sync button up to events~~
* ~~Have Sync event call sync on inputExp, inputVal, and workingVal~~
* ~~Modify View code to generate stack of static renderings upon being called in
static mode, which are in possibleChanges~~
  - Move Select button to proper location
  - Do further testing on other microtests
  - Beautify and fix overlaps/ugliness
* Have static rendering come along with a button and an ID
* ~~Make new Event called SelectOption or something to that effect that takes a
choice ID~~
* ~~Have SelectOption make the chosen element of possibleChanges the new
input/working quantities and clear out the old possibilities~~

## Cleanup
* Remove Debug.log from buildSvg and upstate
* Clean "|" code out
* Make ZoneType type instead of using Strings