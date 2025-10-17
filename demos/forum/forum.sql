-- To recreate the database, run this: sudo mariadb forum < forum.sql

DROP DATABASE forum;
CREATE DATABASE forum;
USE forum;


CREATE TABLE Posts (
    id INT AUTO_INCREMENT PRIMARY KEY,
    text TEXT NOT NULL
);



