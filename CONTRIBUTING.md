# General
For the MontiBelle core we use the simplified [GitHub Flow] (https://guides.github.com/introduction/flow/index.html).
The branching model is taken from [here](http://nvie.com/posts/a-successful-git-branching-model/)

Don't forget to create issues and milestones :wink: 


# Contribution Process
## Small Changes

Small changes can be directly pushed to the [develop](https://git.rwth-aachen.de/montibelle/core/tree/develop) branch.


## Bigger Changes/Case Studies
The contribution process for **bigger** changes looks as follows:

1.  Create a new branch from the development branch with an descriptive title for your work
  * avoid "/" in the branch title as the RWTH git server cannot properly deal with it
  * add a new Milestone to the project if your branch represents a Case Study and reference it!

2. Create issues for each sub step 
  * assign to the correct Milestone, Person
  * represent the state of the issue and the area (like SPF, ABP, Streams) via labels [label-overview](https://git.rwth-aachen.de/montibelle/core/labels)
  * An example issue can be found [here](#2)

3. Add your commits to the newly created branch
  * update the issue labels depending on the workstate! (Ready, Working,etc.)
  * if you get stuck do not hesitate to open a "help wanted" issue
  * the overall project state can then be viewed at the [board](https://git.rwth-aachen.de/montibelle/core/boards)

4. Submit a Merge/Pull Request via gitlab
  * make sure that your new work does not break previous results
  * mention someone who can merge your work into the master branch

Note that these are only general guidelines, feedback is welcome.