-- To recreate the database, run this: sudo mariadb < forum.sql

DROP DATABASE IF EXISTS forum;
CREATE DATABASE forum;
USE forum;


CREATE TABLE Threads (
    thread_id INT AUTO_INCREMENT PRIMARY KEY,
    title TEXT NOT NULL
);

CREATE TABLE Posts (
    post_id INT AUTO_INCREMENT PRIMARY KEY,
    thread_id INT NOT NULL REFERENCES Threads(thread_id),
    content TEXT NOT NULL
);

CREATE INDEX IdxPostsInThread ON Posts(thread_id, post_id) 

