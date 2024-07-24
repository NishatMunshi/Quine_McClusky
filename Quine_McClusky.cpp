// author: Nishat Munshi
// last modified : 13 Sep 2023

#include <algorithm>
#include <cassert>
#include <deque>
#include <iostream>
#include <list>
#include <sstream>
#include <string>
#include <vector>

std::list<unsigned> parse_string(const std::string &_string, const unsigned _maxNumberOfTerms) {
    std::stringstream ss(_string);
    unsigned number;
    std::list<unsigned> terms;
    while (ss >> number) {
        if (number >= _maxNumberOfTerms)
            continue;
        terms.push_back(number);
    }
    terms.sort();
    terms.unique();

    return terms;
}

enum bit : char {
    DASH = -1,
    ZERO,
    ONE
};

typedef std::deque<bit> Value;
struct Term {
    Value value;
    bool used = false;
};

typedef std::deque<Term> Section;
typedef std::deque<Section> Column;
typedef std::deque<Column> PrimeImplicantTable;

bool check_if_mergable(const Term &_one, const Term &_two) {
    unsigned numberOfDifferentBits = 0;
    if (_one.value.size() not_eq _two.value.size())
        return false;  // quick error check
    else {
        for (unsigned index = 0; index < _one.value.size(); ++index) {
            if (_one.value[index] not_eq _two.value[index])
                ++numberOfDifferentBits;
        }
    }
    if (numberOfDifferentBits > 1 or numberOfDifferentBits == 0)
        return false;
    else
        return true;
}
Term merge(Term &_first, Term &_second) {
    assert(check_if_mergable(_first, _second));  // quick check

    Term mergedTerm;
    for (unsigned index = 0; index < _first.value.size(); ++index) {
        if (_first.value[index] == _second.value[index])
            mergedTerm.value.push_back(_first.value[index]);
        else
            mergedTerm.value.push_back(DASH);
    }

    // mark both first and second as used;
    _first.used = _second.used = true;
    return mergedTerm;
}
Column construct_first_column(const std::list<unsigned> &_terms, const unsigned _numberOfVariables) {
    // make a list fo pairs of numbers, first showing the actual number and second being the number of Ones in it
    std::list<std::pair<unsigned, unsigned>> numbersWithNumberOfOnesInThem;
    auto number_of_ones = [](unsigned _number) {
        unsigned numberOfOnes = 0;
        while (_number not_eq 0) {
            numberOfOnes += _number bitand 1;
            _number >>= 1;
        }
        return numberOfOnes;
    };
    for (auto term : _terms) {
        auto numberOfOnes = number_of_ones(term);
        numbersWithNumberOfOnesInThem.push_back({term, numberOfOnes});
    }

    // make Sections of unsigned numbers by sorting them in order
    numbersWithNumberOfOnesInThem.sort([](const std::pair<unsigned, unsigned> &_x, const std::pair<unsigned, unsigned> &_y) { return _x.second < _y.second; });
    // std::sort(numbersWithNumberOfOnesInThem.begin(), numbersWithNumberOfOnesInThem.end(), [](const std::pair<unsigned, unsigned> &_x, const std::pair<unsigned, unsigned> &_y)
    //           { return _x.second < _y.second; });
    auto number_to_Term = [](unsigned _number, unsigned _numberOfVariables) {
        bool One;
        Term oneTerm;
        while (_number not_eq 0) {
            One = _number bitand 1;
            _number >>= 1;
            if (One)
                oneTerm.value.push_front(ONE);
            else
                oneTerm.value.push_front(ZERO);
        }
        // fill leading zeros if necessary
        while (oneTerm.value.size() < _numberOfVariables) {
            oneTerm.value.push_front(ZERO);
        }
        return oneTerm;
    };
    Section oneSection;
    Column col0;
    for (unsigned numberOfOnes = 0; not numbersWithNumberOfOnesInThem.empty(); ++numberOfOnes) {
        // for (auto pair : numbersWithNumberOfOnesInThem)
        // {
        //     if (pair.second == numberOfOnes)
        //     {
        //         oneSection.push_back(number_to_Term(pair.first, _numberOfVariables));
        //     }
        // }
        while (numberOfOnes == numbersWithNumberOfOnesInThem.front().second) {
            oneSection.push_back(number_to_Term(numbersWithNumberOfOnesInThem.front().first, _numberOfVariables));
            numbersWithNumberOfOnesInThem.pop_front();
        }
        if (not oneSection.empty())
            col0.push_back(oneSection);
        oneSection.clear();
    }
    return col0;
}
Column construct_next_column(Column &_col) {
    Column resultCol;
    Section oneSection;
    for (unsigned sectionIndex = 0; sectionIndex < _col.size() - 1; ++sectionIndex) {
        auto nextSectionIndex = sectionIndex + 1;
        for (auto &firstSectionMember : _col[sectionIndex]) {
            for (auto &nextSectionMember : _col[nextSectionIndex]) {
                bool mergable = check_if_mergable(firstSectionMember, nextSectionMember);
                if (mergable) {
                    auto mergedTerm = merge(firstSectionMember, nextSectionMember);
                    bool duplicateFlag = false;
                    for (auto term : oneSection) {
                        if (term.value == mergedTerm.value) {
                            duplicateFlag = true;
                            break;
                        }
                    }
                    if (not duplicateFlag)
                        oneSection.push_back(mergedTerm);
                }
            }
        }
        if (not oneSection.empty()) {
            resultCol.push_back(oneSection);
            oneSection.clear();
        }
    }
    return resultCol;
}

auto primeImplicant_to_numbers(const Term &_primeImplicant) {
    std::vector<unsigned> numbers;
    // insert first number to modify
    numbers.push_back(0);
    for (auto &bit : _primeImplicant.value) {
        if (bit == ZERO) {
            for (auto &number : numbers)
                number <<= 1;
        } else if (bit == ONE) {
            for (auto &number : numbers) {
                number <<= 1;
                number xor_eq 1;
            }
        }

        // if we see a dash
        else {
            auto size = numbers.size();
            for (unsigned index = 0; index < size; ++index) {
                // push 0 in the original number
                numbers[index] <<= 1;
                // create new number for it and push 1 in it
                auto newNum = numbers[index];
                newNum xor_eq 1;
                numbers.push_back(newNum);
            }
        }
    }
    std::sort(numbers.begin(), numbers.end());
    return numbers;
}
auto construct_primeImplicant_table(const std::list<unsigned> &_terms, const unsigned _numberOfVariables) {
    assert(not _terms.empty());  // quick check

    auto firstCol = construct_first_column(_terms, _numberOfVariables);
    PrimeImplicantTable table;
    table.push_back(firstCol);

    auto nextCol = construct_next_column(table.back());
    while (not nextCol.empty()) {
        table.push_back(nextCol);
        nextCol = construct_next_column(table.back());
    }

    return table;
}

auto list_of_primeImplicants(const PrimeImplicantTable &_table) {
    // make a list of prime implicants from the first table
    std::vector<Term> primeImplicants;
    for (auto &col : _table) {
        for (auto &sec : col) {
            for (auto &term : sec) {
                if (not term.used) {
                    primeImplicants.push_back(term);
                }
            }
        }
    }
    return primeImplicants;
}
auto construct_essential_primeImplecant_table(const PrimeImplicantTable &_table, const std::list<unsigned> &_minTerms, const unsigned _numberOfVaribles) {
    auto primeImplicants = list_of_primeImplicants(_table);
    auto numberOfPrimeImplicants = primeImplicants.size();

    // making the table whose columns indicate the mineterms in order of the list "_minTerms"
    std::vector<std::vector<bool>> table;

    // fill the table with falses
    auto tempRow = new std::vector<bool>;
    for (unsigned columnIndex = 0; columnIndex < _minTerms.size(); ++columnIndex) {
        tempRow->push_back(false);
    }
    for (unsigned rowIndex = 0; rowIndex < numberOfPrimeImplicants; ++rowIndex) {
        table.push_back(*tempRow);
    }
    delete tempRow;

    auto get_index = [](const std::list<unsigned> _terms, const unsigned _value) {
        int index = 0;
        for (auto &term : _terms) {
            if (term == _value)
                return index;
            ++index;
        }
        return -1;
    };

    // mark the primeImplicants' contributions
    for (unsigned rowIndex = 0; rowIndex < numberOfPrimeImplicants; ++rowIndex) {
        auto contributions = primeImplicant_to_numbers(primeImplicants[rowIndex]);
        for (auto &contributor : contributions) {
            for (auto &minTerm : _minTerms) {
                auto columnIndex = get_index(_minTerms, minTerm);
                if (contributor == minTerm) {
                    table[rowIndex][columnIndex] = true;
                }
            }
        }
    }
    return table;
}

auto get_essential_primeImplicant_indices(const std::vector<std::vector<bool>> &_essentialPrimeImplicantTable) {
    // make a container for essential prime implicant indices
    std::list<unsigned> essentialPrimeImplicantIndices;

    auto numberOfMinTerms = _essentialPrimeImplicantTable[0].size();
    // index of Cotributors for each column, it is a vector of vectors
    std::vector<std::vector<unsigned>> indecesOfContributors(numberOfMinTerms);
    for (unsigned columnIndex = 0; columnIndex < numberOfMinTerms; ++columnIndex) {
        for (unsigned rowIndex = 0; rowIndex < _essentialPrimeImplicantTable.size(); ++rowIndex) {
            if (_essentialPrimeImplicantTable[rowIndex][columnIndex] == true) {
                indecesOfContributors[columnIndex].push_back(rowIndex);
            }
        }
        // find  how many contributors there are in this column
        auto numberOfContributors = indecesOfContributors[columnIndex].size();

        // if there is only one contributor then push it in the grand list
        if (numberOfContributors == 1)
            essentialPrimeImplicantIndices.push_back(indecesOfContributors[columnIndex].front());
    }
    essentialPrimeImplicantIndices.sort();
    essentialPrimeImplicantIndices.unique();

    // now check which minterms are already included by these essential Prime implicants
    std::list<unsigned> indecesOfMinTermsIncluded;
    for (auto &indexOfEssestialPrimeImplicant : essentialPrimeImplicantIndices) {
        for (unsigned columnIndex = 0; columnIndex < numberOfMinTerms; ++columnIndex) {
            if (_essentialPrimeImplicantTable[indexOfEssestialPrimeImplicant][columnIndex] == true)
                indecesOfMinTermsIncluded.push_back(columnIndex);
        }
    }
    indecesOfMinTermsIncluded.sort();
    indecesOfMinTermsIncluded.unique();

    // if we already ahve included every minterm then just return. no need to do anything else
    if (indecesOfMinTermsIncluded.size() == numberOfMinTerms)
        return essentialPrimeImplicantIndices;

    while (true) {
        // find indeces of the minterms that are not included
        std::list<unsigned> indecesOfMinTermsNOTIncluded;
        // first fill it with all the minterms and then we will remove the included ones
        for (unsigned index = 0; index < numberOfMinTerms; ++index) {
            indecesOfMinTermsNOTIncluded.push_back(index);
        }
        for (auto &index : indecesOfMinTermsIncluded) {
            indecesOfMinTermsNOTIncluded.remove(index);
        }

        // check which primeImplicant contribute toward the remaining minterms
        struct contributor {
            unsigned index, numberOfContributionsTowardNotIncludedMinTerms, numberOfContributionsOverall;
        };

        std::list<contributor> contributors;
        for (auto &indexOfMinTerm : indecesOfMinTermsNOTIncluded) {
            for (auto &index : indecesOfContributors[indexOfMinTerm]) {
                contributor x;
                x.index = index;
                contributors.push_back(x);
            }
        }
        contributors.sort([](const contributor &_x, const contributor &_y) { return _x.index < _y.index; });
        contributors.unique([](const contributor &_x, const contributor &_y) { return _x.index == _y.index; });

        for (auto &term : contributors) {
            // .. and what their contribution is towards them
            unsigned numberOfContributuionsTowardsNotIncludedMinTerms = 0;
            unsigned numberOfContributionsOverall = 0;
            for (auto &indexOfNotIncludedMinTerm : indecesOfMinTermsNOTIncluded) {
                if (_essentialPrimeImplicantTable[term.index][indexOfNotIncludedMinTerm] == true) {
                    ++numberOfContributuionsTowardsNotIncludedMinTerms;
                    ++numberOfContributionsOverall;
                }
            }
            // .. and what their contribution is overall
            for (auto &indexOfIncludedMinterm : indecesOfMinTermsIncluded) {
                if (_essentialPrimeImplicantTable[term.index][indexOfIncludedMinterm] == true)
                    ++numberOfContributionsOverall;
            }
            term.numberOfContributionsTowardNotIncludedMinTerms = numberOfContributuionsTowardsNotIncludedMinTerms;
            term.numberOfContributionsOverall = numberOfContributionsOverall;
        }

        // ... sort them in descending order of number of numberOfContributionsTowardNotIncludedMinTerms
        contributors.sort([](const contributor &_x, const contributor &_y) { return _x.numberOfContributionsTowardNotIncludedMinTerms > _y.numberOfContributionsTowardNotIncludedMinTerms; });

        // now if two contributors have equal numberOfContributionsTowardNotIncludedMinTerms
        // sort them in descending order of number of numberOfContributionsOverall
        contributors.sort([](const contributor &_x, const contributor &_y) { return _x.numberOfContributionsOverall > _y.numberOfContributionsOverall; });

        assert(not indecesOfMinTermsNOTIncluded.empty());
        // take contributors one by one and mark what they contribute.
        // when all minterms are taken then stop
        // push the most contributing so far
        essentialPrimeImplicantIndices.push_back(contributors.front().index);
        contributors.pop_front();

        // find out what it contributes;
        for (auto &indexOfNotIncludedMinTerm : indecesOfMinTermsNOTIncluded) {
            if (_essentialPrimeImplicantTable[essentialPrimeImplicantIndices.back()][indexOfNotIncludedMinTerm] == true)
                indecesOfMinTermsIncluded.push_back(indexOfNotIncludedMinTerm);
        }
        indecesOfMinTermsIncluded.sort();
        indecesOfMinTermsIncluded.unique();

        // if all remaining minterms are taken then break
        if (indecesOfMinTermsIncluded.size() >= numberOfMinTerms)
            break;
    }

    essentialPrimeImplicantIndices.sort();
    return essentialPrimeImplicantIndices;
}

auto get_simplified_function(const std::vector<Term> &_listOfPrimeImplicants, const std::list<unsigned> &_essentialPrimeImplicantIndices) {
    auto term_to_string = [](const Term &_term) {
        char letter = 'A';
        std::string string;
        for (auto &bit : _term.value) {
            if (bit == ZERO) {
                string.push_back(letter);
                string.push_back('\'');
            } else if (bit == ONE) {
                string.push_back(letter);
            }
            ++letter;
        }
        return string;
    };

    std::list<Term> essentialPrimeImplicants;
    std::string returnString("F = ");
    for (auto &index : _essentialPrimeImplicantIndices) {
        essentialPrimeImplicants.push_back(_listOfPrimeImplicants[index]);
        returnString += term_to_string(essentialPrimeImplicants.back()) + std::string(" + ");
    }

    // remove the last " + "
    returnString.pop_back();
    returnString.pop_back();
    returnString.pop_back();

    return returnString;
};

int main() {
    std::cout << "Enter number of variables: ";
    unsigned int numberOfVariables;
    std::cin >> numberOfVariables;

    // ignore whatever character is in the input buffer
    std::string string;
    std::getline(std::cin, string);

    std::cout << "Enter all minterms: ";
    std::getline(std::cin, string, '\n');
    unsigned maxNumberOfTerms = 1 << numberOfVariables;
    auto minTerms = parse_string(string, maxNumberOfTerms);

    std::cout << "Enter all don't care terms: ";
    std::getline(std::cin, string, '\n');
    auto dontCareTerms = parse_string(string, maxNumberOfTerms);

    // check if any term is common and inform the user that they made a mistake
    for (auto &term0 : minTerms) {
        for (auto &term1 : dontCareTerms) {
            if (term0 == term1) {
                std::cout << "minterm and don't care term cannot be equal\n";
                return 0;
            }
        }
    }

    auto terms = minTerms;
    terms.merge(dontCareTerms);

    auto primeImplicantTable = construct_primeImplicant_table(terms, numberOfVariables);
    auto listOfPrimeImplicants = list_of_primeImplicants(primeImplicantTable);
    auto essentialPrimeImplicantTable = construct_essential_primeImplecant_table(primeImplicantTable, minTerms, numberOfVariables);
    auto essentialPrimeImplicantIndices = get_essential_primeImplicant_indices(essentialPrimeImplicantTable);

    auto function = get_simplified_function(listOfPrimeImplicants, essentialPrimeImplicantIndices);
    std::cout << "The simplified function is: " << function << "\n";

    return 0;
}
