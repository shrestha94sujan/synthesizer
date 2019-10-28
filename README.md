# Command to add AlloyEngine to your local
This tool depends on the AlloyEngine. In order to make the build working, we need to add the AlloyEngine in our local maven repository.

First go to the project root folder, and then run this command.
```
mvn install:install-file -Dfile=libs/AlloyEngine.jar -DgroupId=edu.virginia.cs -DartifactId=AlloyEngine -Dversion=1.0 -Dpackaging=jar
```

# Command to build the project

First go to the root folder of this project, and then run this command to build the project.

```$xslt
mvn clean install
```

Now, there should be a ${projectBaseDir}/target folder generated and two .jar files are also created.

1. synthesizer-1.0-jar-with-dependencies.jar
2. synthesizer-1.0.jar

The __synthesizer-1.0-jar-with-dependencies.jar__ is what we needed.

# Steps to run the test 
In the ${projectBaseDir}, there is a folder named __models__. You will find many __.als__ files.

Some of them are basic .als files:
```$xslt
util
AssociationMappings.als
ORMStrategies.als
relationalModel.als
assertions.als
Declaration.als
```

The other ones are application models. So far, they are:
```$xslt
customerOrderObjectModel.als
flagship.als
ecommerce.als
CSOS.als
decider.als
```

The __customerOrderObjectModel.als__ is the smallest one and takes only seconds to run. You should play with it first.

# Try with a real example
First create a new workspace folder out of this project, say: 
```
mkdir -p ~/toolplay/customerOrder
```

Then run this command:
```$xslt
java -jar ${synthesizer}/target/synthesizer-1.0-jar-with-dependencies.jar ~/toolplay/customerOrder ${synthesizer}/models/customerOrderObjectModel.als 20000 false 500
```

Arguments:
```$xslt
1. Workspace (~/toolplay/customerOrder in this case)
2. Path to a .als file (${synthesizer}/models/customerOrderObjectModel.als in this case)
3. The maximum solutions to save (20000 in this case)
4. Whether to store all solutions (False in this case)
5. The range to create test loads (500 in this case, meaning there will be 500 entities created for each class)
```

The output should in the *~/toolplay/customerOrder* folder. There should be some .sql files and .xml files, as well as a *Benchmark* folder with some .sql files.

__Note__: I found there are some confuse of using the arguments in the old cold. This can be easily fixed as you wish. Just update how you want to use it in the main function here:
`https://github.com/ChongTang/synthesizer/blob/master/src/main/java/edu/virginia/cs/Synthesizer.java#L30`