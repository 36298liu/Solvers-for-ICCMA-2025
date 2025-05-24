/**
 * @file 		AF.cpp
 * @class 		AF
 * @brief 		Class encompassing an Argumentation Framework
 * @author 		Mauro Vallati <m.vallati@hud.ac.uk>
 * @copyright	MIT
 */


#include "AF.h"

/**
 * @brief 	Simple constructor
 */
AF::AF()
{
	this->arguments = new SetArguments();
	//this->raw_attacks = map<int, int >();
	//this->attacks = map<Argument *, SetArguments *>();
	//this->attackers = map<Argument *, SetArguments *>();
}


AF::~AF()
{
	// TODO Auto-generated destructor stub
}


string AF::trim(string s)
{
	size_t init = s.find_first_not_of(" ");
	size_t end = s.find_last_not_of(" ");

	if (init == string::npos)
		init = 0;

	if (end == string::npos)
		end = s.size();

	return s.substr(init, end - init + 1);
}

/**
 * @brief 		Method for parsing a ASPARTIX compliant file
 * @details		It uses part of the code from Samer Nofal's, University of Liverpool
 * @param[in] file A string representing the (relative/absolute) path to the ASPARTIX compliant file
 * @retval bool It returns `True` if it can correctly parse the file, `False` otherwise
 */
bool AF::readFile(string file)
{
	string inLine;
	ifstream infile;
	infile.open(file.c_str());
	if (!infile.good())
		return false;

	size_t init = 0;
	size_t index;
	//如果存在
	if((index = file.find("crusti"))!=string::npos)
	{
		do
		{
			getline(infile, inLine);
			if (debug)
				cerr << inLine << endl;
			if(!inLine.empty())
			{
				if ((init = inLine.find("f")) != string::npos)
				{
					string number=this->trim(inLine.substr(init+1));
					//cerr<<number<<endl;
					int arg_number = stoi(number);
					for(int i=1; i < arg_number+1 ; i++)
					{
						string arg = std::to_string(i);
						this->arguments->add_Argument(
						new Argument(arg,i,this));
					}
				}
				else
				{
					size_t split = inLine.find(" ");
					if (split == string::npos)
							return false;

					if (debug)
					{
						cerr<<inLine.substr(0,split)<<endl;
						cerr << "source"<<this->trim(inLine.substr(0, split)) << endl;
						cerr << "target"<<this->trim(
								inLine.substr(split + 1)) << endl;
					}
					string str1=this->trim(inLine.substr(0, split));
					string str2=this->trim(inLine.substr(split + 1));
					int num1 = stoi(str1);
					int num2 = stoi(str2);
					Argument *source = this->getArgumentByNumber(num1);
					Argument *target = this->getArgumentByNumber(num2);
					source->add_attacks(target);
					target->add_attackers(source);
				}

			}
		}while (!infile.eof());
	}
	else
	{
		int i=1;
		do
		{
			getline(infile, inLine);
			if (debug)
				cerr << inLine << endl;
			if (!inLine.empty())
			{
				if ((init = inLine.find("p af")) != string::npos)
				{
					continue;
				}
				else if((init = inLine.find("#")) != string::npos)
				{
					if (debug)
					{
						cerr<< this->trim(
										inLine.substr(1))
								<< endl;
					}
					//cerr<<this->numArgs()<<endl;争议是从0开始编号的，但算例是从1开始编号的
					/*
					this->arguments->add_Argument(
							new Argument(
									this->trim(
											inLine.substr(1)),
									this->numArgs()+1, this));
*/
					string arg = std::to_string(i);
					this->arguments->add_Argument(new 								Argument(arg,i,this));
				}
				else
				{
					size_t split = inLine.find(" ");
					if (split == string::npos)
							return false;

					if (debug)
					{
						cerr<<inLine.substr(0,split)<<endl;
						cerr << "source"<<this->trim(inLine.substr(0, split)) << endl;
						cerr << "target"<<this->trim(
								inLine.substr(split + 1)) << endl;
					}
					string str1=this->trim(inLine.substr(0, split));
					string str2=this->trim(inLine.substr(split + 1));
					int num1 = stoi(str1);
					int num2 = stoi(str2);
					Argument *source = this->getArgumentByNumber(num1);
					Argument *target = this->getArgumentByNumber(num2);
					source->add_attacks(target);
					target->add_attackers(source);
				}
			}
			i++;
		} while (!infile.eof());
	}
	if (debug)
	{
		for (SetArgumentsIterator it = this->arguments->begin();
				it != this->arguments->end(); it++)
			cerr << (*it) << ", ";
		cerr << endl;
	}
	infile.close();
	return true;
}


/**
 * @brief		This method returns the pointer to the Argument whose name is given as parameter
 * @param[in] name	 The name of the argument
 * @retval Argument* The pointer to the Argument object, or NULL if not found
 */
Argument *AF::getArgumentByName(string name)
{
	return this->arguments->getArgumentByName(name);
}

/**
 * @brief 	Returns the number of arguments
 * @retval int
 */
int AF::numArgs()
{
	return this->arguments->cardinality();
}


/**
 * @brief		This method returns the pointer to the Argument whose identification number is given as parameter
 * @param[in] num	 The name of the argument
 * @retval Argument* The pointer to the Argument object, or NULL if not found
 */
Argument *AF::getArgumentByNumber(int num)
{
	return this->arguments->getArgumentByNumber(num);
}

/**
 * @brief 	Begin of the iterator for the set of arguments
 * @retval SetArgumentsIterator An iterator pointing at the first of the elements of the set of arguments
 */
SetArgumentsIterator AF::begin()
{
	return this->arguments->begin();
}

/**
 * @brief 	End of the iterator for the set of arguments
 * @retval SetArgumentsIterator An iterator pointing at the last of the elements of the set of arguments
 */
SetArgumentsIterator AF::end()
{
	return this->arguments->end();
}

/**
 * @brief	Returns a pointer to the set of arguments
 * @retval SetArguments*
 */
SetArguments *AF::get_arguments() const
{
	return this->arguments;
}
